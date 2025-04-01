import Lean.Elab.Tactic

import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Chi
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Lookups.ChiBase
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.NormalizeRho.All
import Examples.Scroll.Keccak.Soundness.RhoParts
import Examples.Scroll.Keccak.Util


namespace Keccak.Soundness

  lemma s_input_parts_0_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
    Decode.expr [
      (4, cell_manager c round 336),
      (4, cell_manager c round 337),
      (4, cell_manager c round 338),
      (4, cell_manager c round 339),
      (4, cell_manager c round 340),
      (4, cell_manager c round 341),
      (4, cell_manager c round 342),
      (4, cell_manager c round 343),
      (4, cell_manager c round 344),
      (4, cell_manager c round 345),
      (4, cell_manager c round 346),
      (4, cell_manager c round 347),
      (4, cell_manager c round 396),
      (4, cell_manager c round 397),
      (4, cell_manager c round 398),
      (4, cell_manager c round 399)
    ] =
    os c round 0 0
  := by
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells
    ] at h_s_input_parts
    exact h_s_input_parts

  -- lemma s_parts'_transform_0_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
  --   os c round 0 0 =
  --   sorry
  -- := by
  --   have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
  --   simp [
  --     keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
  --     s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
  --     s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
  --   ] at h_s_transform
  --   rewrite [←s_input_parts_0_0]
  --   <;> sorry

  -- Normalize (rot 0 (os c round 0 0)) =
  -- Decode [cells 756..767,816..819] =
  -- Decode s_parts' c round 0 0 =
  -- Decode os_parts c round 0 0

  -- Normalized by rho
  -- Pi just shuffles
  -- Chi has normalised input

  lemma self_normalize_of_normalized [NeZero P] (x: ZMod P) (h_P: 585 < P) (h_x: x.val = Normalize.normalize_unpacked x' 4):
    x = Normalize.normalize_unpacked x.val 4
  := by
      apply ZMod.val_injective
      simp [h_x]
      rw [
        Normalize.normalize_unpacked_idempotent,
        Nat.mod_eq_of_lt
      ]
      exact lt_of_le_of_lt
        Normalize.normalize_unpacked_4_le
        h_P

  def bit_invert (x width: ℕ) := (~~~(BitVec.ofNat (width*BIT_COUNT) x)).toNat

  lemma bit_invert_normalized_eq_xor (h: x = Normalize.normalize_unpacked x' 4):
    bit_invert x 4 = 4095 ^^^ x
  := by
    simp only [
      h,
      bit_invert.eq_def,
    ]
    rewrite [show 4095 = (4095#192).toNat by decide]
    simp only [
      Normalize.normalize_unpacked_to_bitvec,
      ←BitVec.toNat_xor,
      keccak_constants, Nat.reduceMul,
    ]
    rewrite [BitVec.ofNat_toNat]
    have : (BitVec.setWidth 192 (
        ~~~BitVec.setWidth 12 (
          BitVec.ofNat 192 x' &&&
          BitVec.ofNat 192 Normalize.mask &&&
          BitVec.setWidth 192 (BitVec.allOnes 12))
      )) = (
        4095#192 ^^^
        BitVec.ofNat 192 x' &&&
        BitVec.ofNat 192 Normalize.mask &&& BitVec.setWidth 192 (BitVec.allOnes 12)
      )
    := by
      simp only [Normalize.mask_bitvec_ofNat, Normalize.mask_bitvec.eq_def]
      bv_decide
    rewrite [←this]
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    bv_omega

  lemma bit_invert_to_bitvec:
    (BitVec.ofNat (width*BIT_COUNT) (bit_invert x width)).toNat =
    bit_invert x width
  := by
    simp [
      bit_invert.eq_def, keccak_constants
    ]
    rw [Nat.mod_eq_of_lt (a := _ - _ - _) (by omega)]

  lemma chi_base_0_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: 2^(4*BIT_COUNT) < P)
    (h_row: row < 730)
    (h_70: (c.get_advice 70 row).val = Normalize.normalize_unpacked x0 4)
    (h_71: (c.get_advice 71 row).val = Normalize.normalize_unpacked x1 4)
    (h_72: (c.get_advice 72 row).val = Normalize.normalize_unpacked x2 4)
  :
    c.get_advice 105 row = Normalize.normalize_unpacked (
      (c.get_advice 70 row).val ^^^ (
        (bit_invert (c.get_advice 71 row).val 4) &&&
        (c.get_advice 72 row).val
      )
    ) 4
  := by
    simp [keccak_constants] at h_P
    have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
    have h_chi_base := Proofs.chi_base_of_meets_constraints ⟨0, by simp [keccak_constants]⟩ 0 h_meets_constraints row (by omega)
    obtain ⟨lookup_row, h_lookup_row⟩ := h_chi_base
    simp [
      chi_base, chi_base_input', keccak_constants,
      chi_base_input, chi_base_output
    ] at h_lookup_row
    symm at h_lookup_row
    apply Lookups.ChiBase.apply_transform_table at h_lookup_row
    set lookup_row' := (if lookup_row < 625 then lookup_row else 0)
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_70' := (self_normalize_of_normalized (c.get_advice 70 row) (by omega) h_70)
    have h_71' := (self_normalize_of_normalized (c.get_advice 71 row) (by omega) h_71)
    have h_72' := (self_normalize_of_normalized (c.get_advice 72 row) (by omega) h_72)
    have := Lookups.ChiBase.output_eq_transformed_input
      h_70' h_71' h_72'
      h_lookup_row.1
      (by simp [keccak_constants]; omega)
    rewrite [bit_invert_normalized_eq_xor h_71]
    rewrite [h_70', h_71', h_72']
    simp
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_4095_4
    ]
    rewrite [h_70', h_71', h_72'] at this
    simp at this
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Normalize.and_normalize,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_4095_4,
      Normalize.normalize_unpacked_idempotent,
    ] at this
    rewrite [←this, h_lookup_row.2]
    simp

  lemma chi_base_1_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: 2^(4*BIT_COUNT) < P)
    (h_row: row < 730)
    (h_75: (c.get_advice 75 row).val = Normalize.normalize_unpacked x0 4)
    (h_76: (c.get_advice 76 row).val = Normalize.normalize_unpacked x1 4)
    (h_77: (c.get_advice 77 row).val = Normalize.normalize_unpacked x2 4)
  :
    c.get_advice 110 row = Normalize.normalize_unpacked (
      (c.get_advice 75 row).val ^^^ (
        (bit_invert (c.get_advice 76 row).val 4) &&&
        (c.get_advice 77 row).val
      )
    ) 4
  := by
    simp [keccak_constants] at h_P
    have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
    have h_chi_base := Proofs.chi_base_of_meets_constraints ⟨1, by simp [keccak_constants]⟩ 0 h_meets_constraints row (by omega)
    obtain ⟨lookup_row, h_lookup_row⟩ := h_chi_base
    simp [
      chi_base, chi_base_input', keccak_constants,
      chi_base_input, chi_base_output
    ] at h_lookup_row
    symm at h_lookup_row
    apply Lookups.ChiBase.apply_transform_table at h_lookup_row
    set lookup_row' := (if lookup_row < 625 then lookup_row else 0)
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_75' := (self_normalize_of_normalized (c.get_advice 75 row) (by omega) h_75)
    have h_76' := (self_normalize_of_normalized (c.get_advice 76 row) (by omega) h_76)
    have h_77' := (self_normalize_of_normalized (c.get_advice 77 row) (by omega) h_77)
    have := Lookups.ChiBase.output_eq_transformed_input
      h_75' h_76' h_77'
      h_lookup_row.1
      (by simp [keccak_constants]; omega)
    rewrite [bit_invert_normalized_eq_xor h_76]
    rewrite [h_75', h_76', h_77']
    simp
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_4095_4
    ]
    rewrite [h_75', h_76', h_77'] at this
    simp at this
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
      Normalize.and_normalize,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_4095_4,
      Normalize.normalize_unpacked_idempotent,
    ] at this
    rewrite [←this, h_lookup_row.2]
    simp


  lemma separate_decodes_step_1
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^12)
    (h_x4: x4 < 2^12)
    (h_x5: x5 < 2^12)
  :
    (x0 <<< 12 ^^^ x1 <<< 12 &&& x2 <<< 12) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 12 + x3) ^^^ (x1 <<< 12 + x4) &&& (x2 <<< 12 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 12 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 12 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 12 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 12 ≤ 24 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 12 ≤ 24 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 12 ≤ 24 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 12) (width2 := 24) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (show 4096 < 16777216 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (show 4096 < 16777216 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (show 4096 < 16777216 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (show 4096 < 16777216 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (show 4096 < 16777216 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (show 4096 < 16777216 by trivial)),
        Nat.mod_eq_of_lt (show x0 <<< 12 < 16777216 by omega),
        Nat.mod_eq_of_lt (show x1 <<< 12 < 16777216 by omega),
        Nat.mod_eq_of_lt (show x2 <<< 12 < 16777216 by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_2
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^24)
    (h_x4: x4 < 2^24)
    (h_x5: x5 < 2^24)
  :
    (x0 <<< 24 ^^^ x1 <<< 24 &&& x2 <<< 24) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 24 + x3) ^^^ (x1 <<< 24 + x4) &&& (x2 <<< 24 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 24 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 24 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 24 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 24 ≤ 36 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 24 ≤ 36 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 24 ≤ 36 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 24) (width2 := 36) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (show 2^12 < 68719476736 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (show 2^12 < 68719476736 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (show 2^12 < 68719476736 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (show 2^24 < 68719476736 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (show 2^24 < 68719476736 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (show 2^24 < 68719476736 by trivial)),
        Nat.mod_eq_of_lt (show x0 <<< 24 < 68719476736 by omega),
        Nat.mod_eq_of_lt (show x1 <<< 24 < 68719476736 by omega),
        Nat.mod_eq_of_lt (show x2 <<< 24 < 68719476736 by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 16777216 := by
        apply Nat.xor_lt_two_pow (n := 24)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_2_lt :
    Normalize.normalize_unpacked x1 4 <<< 12 +
    Normalize.normalize_unpacked x2 4 < 2^24
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    omega

  lemma separate_decodes_step_3
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^36)
    (h_x4: x4 < 2^36)
    (h_x5: x5 < 2^36)
  :
    (x0 <<< 36 ^^^ x1 <<< 36 &&& x2 <<< 36) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 36 + x3) ^^^ (x1 <<< 36 + x4) &&& (x2 <<< 36 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 36 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 36 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 36 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 36 ≤ 48 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 36 ≤ 48 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 36 ≤ 48 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 36) (width2 := 48) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (show 2^12 < 281474976710656 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (show 2^12 < 281474976710656 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (show 2^12 < 281474976710656 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (show 2^36 < 281474976710656 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (show 2^36 < 281474976710656 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (show 2^36 < 281474976710656 by trivial)),
        Nat.mod_eq_of_lt (show x0 <<< 36 < 281474976710656 by omega),
        Nat.mod_eq_of_lt (show x1 <<< 36 < 281474976710656 by omega),
        Nat.mod_eq_of_lt (show x2 <<< 36 < 281474976710656 by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 68719476736 := by
        apply Nat.xor_lt_two_pow (n := 36)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_3_lt :
    Normalize.normalize_unpacked x1 4 <<< 24 +
    (Normalize.normalize_unpacked x2 4 <<< 12 +
    Normalize.normalize_unpacked x3 4) < 2^36
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    omega

  lemma separate_decodes_step_4
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^48)
    (h_x4: x4 < 2^48)
    (h_x5: x5 < 2^48)
  :
    (x0 <<< 48 ^^^ x1 <<< 48 &&& x2 <<< 48) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 48 + x3) ^^^ (x1 <<< 48 + x4) &&& (x2 <<< 48 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 48 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 48 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 48 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 48 ≤ 60 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 48 ≤ 60 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 48 ≤ 60 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 48) (width2 := 60) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (show 2^12 < 1152921504606846976 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (show 2^12 < 1152921504606846976 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (show 2^12 < 1152921504606846976 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (show 2^48 < 1152921504606846976 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (show 2^48 < 1152921504606846976 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (show 2^48 < 1152921504606846976 by trivial)),
        Nat.mod_eq_of_lt (show x0 <<< 48 < 1152921504606846976 by omega),
        Nat.mod_eq_of_lt (show x1 <<< 48 < 1152921504606846976 by omega),
        Nat.mod_eq_of_lt (show x2 <<< 48 < 1152921504606846976 by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 281474976710656 := by
        apply Nat.xor_lt_two_pow (n := 48)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_4_lt :
    Normalize.normalize_unpacked x1 4 <<< 36 +
    (Normalize.normalize_unpacked x2 4 <<< 24 +
    (Normalize.normalize_unpacked x3 4 <<< 12 +
    Normalize.normalize_unpacked x4 4)) < 2^48
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    omega

  lemma separate_decodes_step_5
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^60)
    (h_x4: x4 < 2^60)
    (h_x5: x5 < 2^60)
  :
    (x0 <<< 60 ^^^ x1 <<< 60 &&& x2 <<< 60) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 60 + x3) ^^^ (x1 <<< 60 + x4) &&& (x2 <<< 60 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 60 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 60 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 60 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 60 ≤ 72 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 60 ≤ 72 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 60 ≤ 72 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 60) (width2 := 72) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (show 2^12 < 4722366482869645213696 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (show 2^12 < 4722366482869645213696 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (show 2^12 < 4722366482869645213696 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (show 2^60 < 4722366482869645213696 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (show 2^60 < 4722366482869645213696 by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (show 2^60 < 4722366482869645213696 by trivial)),
        Nat.mod_eq_of_lt (show x0 <<< 60 < 4722366482869645213696 by omega),
        Nat.mod_eq_of_lt (show x1 <<< 60 < 4722366482869645213696 by omega),
        Nat.mod_eq_of_lt (show x2 <<< 60 < 4722366482869645213696 by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 1152921504606846976 := by
        apply Nat.xor_lt_two_pow (n := 60)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_5_lt :
    Normalize.normalize_unpacked x1 4 <<< 48 +
    (Normalize.normalize_unpacked x2 4 <<< 36 +
    (Normalize.normalize_unpacked x3 4 <<< 24 +
    (Normalize.normalize_unpacked x4 4 <<< 12 +
    Normalize.normalize_unpacked x5 4))) < 2^60
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    omega

  lemma separate_decodes_step_6
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^72)
    (h_x4: x4 < 2^72)
    (h_x5: x5 < 2^72)
  :
    (x0 <<< 72 ^^^ x1 <<< 72 &&& x2 <<< 72) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 72 + x3) ^^^ (x1 <<< 72 + x4) &&& (x2 <<< 72 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 72 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 72 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 72 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 72 ≤ 84 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 72 ≤ 84 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 72 ≤ 84 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 72) (width2 := 84) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 4722366482869645213696 := by
        apply Nat.xor_lt_two_pow (n := 72)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_6_lt :
    Normalize.normalize_unpacked x1 4 <<< 60 +
    (Normalize.normalize_unpacked x2 4 <<< 48 +
    (Normalize.normalize_unpacked x3 4 <<< 36 +
    (Normalize.normalize_unpacked x4 4 <<< 24 +
    (Normalize.normalize_unpacked x5 4 <<< 12 +
    Normalize.normalize_unpacked x6 4)))) < 2^72
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    omega

  lemma separate_decodes_step_7
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^84)
    (h_x4: x4 < 2^84)
    (h_x5: x5 < 2^84)
  :
    (x0 <<< 84 ^^^ x1 <<< 84 &&& x2 <<< 84) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 84 + x3) ^^^ (x1 <<< 84 + x4) &&& (x2 <<< 84 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 84 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 84 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 84 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 84 ≤ 96 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 84 ≤ 96 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 84 ≤ 96 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 84) (width2 := 96) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 19342813113834066795298816 := by
        apply Nat.xor_lt_two_pow (n := 84)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_7_lt :
    Normalize.normalize_unpacked x1 4 <<< 72 +
    (Normalize.normalize_unpacked x2 4 <<< 60 +
    (Normalize.normalize_unpacked x3 4 <<< 48 +
    (Normalize.normalize_unpacked x4 4 <<< 36 +
    (Normalize.normalize_unpacked x5 4 <<< 24 +
    (Normalize.normalize_unpacked x6 4 <<< 12 +
    Normalize.normalize_unpacked x7 4))))) < 2^84
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    omega

  lemma separate_decodes_step_8
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^96)
    (h_x4: x4 < 2^96)
    (h_x5: x5 < 2^96)
  :
    (x0 <<< 96 ^^^ x1 <<< 96 &&& x2 <<< 96) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 96 + x3) ^^^ (x1 <<< 96 + x4) &&& (x2 <<< 96 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 96 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 96 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 96 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 96 ≤ 108 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 96 ≤ 108 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 96 ≤ 108 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 96) (width2 := 108) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 79228162514264337593543950336 := by
        apply Nat.xor_lt_two_pow (n := 96)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_8_lt :
    Normalize.normalize_unpacked x1 4 <<< 84 +
    (Normalize.normalize_unpacked x2 4 <<< 72 +
    (Normalize.normalize_unpacked x3 4 <<< 60 +
    (Normalize.normalize_unpacked x4 4 <<< 48 +
    (Normalize.normalize_unpacked x5 4 <<< 36 +
    (Normalize.normalize_unpacked x6 4 <<< 24 +
    (Normalize.normalize_unpacked x7 4 <<< 12 +
    Normalize.normalize_unpacked x8 4)))))) < 2^96
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    omega

  lemma separate_decodes_step_9
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^108)
    (h_x4: x4 < 2^108)
    (h_x5: x5 < 2^108)
  :
    (x0 <<< 108 ^^^ x1 <<< 108 &&& x2 <<< 108) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 108 + x3) ^^^ (x1 <<< 108 + x4) &&& (x2 <<< 108 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 108 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 108 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 108 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 108 ≤ 120 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 108 ≤ 120 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 108 ≤ 120 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 108) (width2 := 120) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 324518553658426726783156020576256 := by
        apply Nat.xor_lt_two_pow (n := 108)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_9_lt :
    Normalize.normalize_unpacked x1 4 <<< 96 +
    (Normalize.normalize_unpacked x2 4 <<< 84 +
    (Normalize.normalize_unpacked x3 4 <<< 72 +
    (Normalize.normalize_unpacked x4 4 <<< 60 +
    (Normalize.normalize_unpacked x5 4 <<< 48 +
    (Normalize.normalize_unpacked x6 4 <<< 36 +
    (Normalize.normalize_unpacked x7 4 <<< 24 +
    (Normalize.normalize_unpacked x8 4 <<< 12 +
    Normalize.normalize_unpacked x9 4))))))) < 2^108
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    omega

  lemma separate_decodes_step_10
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^120)
    (h_x4: x4 < 2^120)
    (h_x5: x5 < 2^120)
  :
    (x0 <<< 120 ^^^ x1 <<< 120 &&& x2 <<< 120) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 120 + x3) ^^^ (x1 <<< 120 + x4) &&& (x2 <<< 120 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 120 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 120 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 120 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 120 ≤ 132 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 120 ≤ 132 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 120 ≤ 132 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 120) (width2 := 132) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 1329227995784915872903807060280344576 := by
        apply Nat.xor_lt_two_pow (n := 120)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_10_lt :
    Normalize.normalize_unpacked x1 4 <<< 108 +
    (Normalize.normalize_unpacked x2 4 <<< 96 +
    (Normalize.normalize_unpacked x3 4 <<< 84 +
    (Normalize.normalize_unpacked x4 4 <<< 72 +
    (Normalize.normalize_unpacked x5 4 <<< 60 +
    (Normalize.normalize_unpacked x6 4 <<< 48 +
    (Normalize.normalize_unpacked x7 4 <<< 36 +
    (Normalize.normalize_unpacked x8 4 <<< 24 +
    (Normalize.normalize_unpacked x9 4 <<< 12 +
    Normalize.normalize_unpacked x10 4)))))))) < 2^120
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    omega

  lemma separate_decodes_step_11
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^132)
    (h_x4: x4 < 2^132)
    (h_x5: x5 < 2^132)
  :
    (x0 <<< 132 ^^^ x1 <<< 132 &&& x2 <<< 132) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 132 + x3) ^^^ (x1 <<< 132 + x4) &&& (x2 <<< 132 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 132 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 132 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 132 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 132 ≤ 144 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 132 ≤ 144 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 132 ≤ 144 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 132) (width2 := 144) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 5444517870735015415413993718908291383296 := by
        apply Nat.xor_lt_two_pow (n := 132)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_11_lt :
    Normalize.normalize_unpacked x1 4 <<< 120 +
    (Normalize.normalize_unpacked x2 4 <<< 108 +
    (Normalize.normalize_unpacked x3 4 <<< 96 +
    (Normalize.normalize_unpacked x4 4 <<< 84 +
    (Normalize.normalize_unpacked x5 4 <<< 72 +
    (Normalize.normalize_unpacked x6 4 <<< 60 +
    (Normalize.normalize_unpacked x7 4 <<< 48 +
    (Normalize.normalize_unpacked x8 4 <<< 36 +
    (Normalize.normalize_unpacked x9 4 <<< 24 +
    (Normalize.normalize_unpacked x10 4 <<< 12 +
    Normalize.normalize_unpacked x11 4))))))))) < 2^132
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    omega

  lemma separate_decodes_step_12
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^144)
    (h_x4: x4 < 2^144)
    (h_x5: x5 < 2^144)
  :
    (x0 <<< 144 ^^^ x1 <<< 144 &&& x2 <<< 144) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 144 + x3) ^^^ (x1 <<< 144 + x4) &&& (x2 <<< 144 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 144 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 144 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 144 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 144 ≤ 156 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 144 ≤ 156 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 144 ≤ 156 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 144) (width2 := 156) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 22300745198530623141535718272648361505980416 := by
        apply Nat.xor_lt_two_pow (n := 144)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_12_lt :
    Normalize.normalize_unpacked x1 4 <<< 132 +
    (Normalize.normalize_unpacked x2 4 <<< 120 +
    (Normalize.normalize_unpacked x3 4 <<< 108 +
    (Normalize.normalize_unpacked x4 4 <<< 96 +
    (Normalize.normalize_unpacked x5 4 <<< 84 +
    (Normalize.normalize_unpacked x6 4 <<< 72 +
    (Normalize.normalize_unpacked x7 4 <<< 60 +
    (Normalize.normalize_unpacked x8 4 <<< 48 +
    (Normalize.normalize_unpacked x9 4 <<< 36 +
    (Normalize.normalize_unpacked x10 4 <<< 24 +
    (Normalize.normalize_unpacked x11 4 <<< 12 +
    Normalize.normalize_unpacked x12 4)))))))))) < 2^144
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    omega

  lemma separate_decodes_step_13
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^156)
    (h_x4: x4 < 2^156)
    (h_x5: x5 < 2^156)
  :
    (x0 <<< 156 ^^^ x1 <<< 156 &&& x2 <<< 156) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 156 + x3) ^^^ (x1 <<< 156 + x4) &&& (x2 <<< 156 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 156 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 156 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 156 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 156 ≤ 168 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 156 ≤ 168 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 156 ≤ 168 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 156) (width2 := 168) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 91343852333181432387730302044767688728495783936 := by
        apply Nat.xor_lt_two_pow (n := 156)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_13_lt :
    Normalize.normalize_unpacked x1 4 <<< 144 +
    (Normalize.normalize_unpacked x2 4 <<< 132 +
    (Normalize.normalize_unpacked x3 4 <<< 120 +
    (Normalize.normalize_unpacked x4 4 <<< 108 +
    (Normalize.normalize_unpacked x5 4 <<< 96 +
    (Normalize.normalize_unpacked x6 4 <<< 84 +
    (Normalize.normalize_unpacked x7 4 <<< 72 +
    (Normalize.normalize_unpacked x8 4 <<< 60 +
    (Normalize.normalize_unpacked x9 4 <<< 48 +
    (Normalize.normalize_unpacked x10 4 <<< 36 +
    (Normalize.normalize_unpacked x11 4 <<< 24 +
    (Normalize.normalize_unpacked x12 4 <<< 12 +
    Normalize.normalize_unpacked x13 4))))))))))) < 2^156
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    have := Normalize.normalize_unpacked_4_le (x := x13)
    omega

  lemma separate_decodes_step_14
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^168)
    (h_x4: x4 < 2^168)
    (h_x5: x5 < 2^168)
  :
    (x0 <<< 168 ^^^ x1 <<< 168 &&& x2 <<< 168) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 168 + x3) ^^^ (x1 <<< 168 + x4) &&& (x2 <<< 168 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 168 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 168 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 168 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 168 ≤ 180 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 168 ≤ 180 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 168 ≤ 180 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 168) (width2 := 180) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 374144419156711147060143317175368453031918731001856 := by
        apply Nat.xor_lt_two_pow (n := 168)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_14_lt :
    Normalize.normalize_unpacked x1 4 <<< 156 +
    (Normalize.normalize_unpacked x2 4 <<< 144 +
    (Normalize.normalize_unpacked x3 4 <<< 132 +
    (Normalize.normalize_unpacked x4 4 <<< 120 +
    (Normalize.normalize_unpacked x5 4 <<< 108 +
    (Normalize.normalize_unpacked x6 4 <<< 96 +
    (Normalize.normalize_unpacked x7 4 <<< 84 +
    (Normalize.normalize_unpacked x8 4 <<< 72 +
    (Normalize.normalize_unpacked x9 4 <<< 60 +
    (Normalize.normalize_unpacked x10 4 <<< 48 +
    (Normalize.normalize_unpacked x11 4 <<< 36 +
    (Normalize.normalize_unpacked x12 4 <<< 24 +
    (Normalize.normalize_unpacked x13 4 <<< 12 +
    Normalize.normalize_unpacked x14 4)))))))))))) < 2^168
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    have := Normalize.normalize_unpacked_4_le (x := x13)
    have := Normalize.normalize_unpacked_4_le (x := x14)
    omega

  lemma separate_decodes_step_15
    (h_x0: x0 < 2^12)
    (h_x1: x1 < 2^12)
    (h_x2: x2 < 2^12)
    (h_x3: x3 < 2^180)
    (h_x4: x4 < 2^180)
    (h_x5: x5 < 2^180)
  :
    (x0 <<< 180 ^^^ x1 <<< 180 &&& x2 <<< 180) +
    (x3 ^^^ x4 &&& x5) =
    (x0 <<< 180 + x3) ^^^ (x1 <<< 180 + x4) &&& (x2 <<< 180 + x5)
  := by
    simp_all
    rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
    rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
    rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
    rewrite [show x3 = (BitVec.ofNat 180 x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
    rewrite [show x4 = (BitVec.ofNat 180 x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
    rewrite [show x5 = (BitVec.ofNat 180 x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
    rewrite [
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      ←BitVec.toNat_and, ←BitVec.toNat_and,
      ←BitVec.toNat_xor, ←BitVec.toNat_xor,
      ←bitvec_setWidth_shift_toNat (show 12 + 180 ≤ 192 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 180 ≤ 192 by trivial),
      ←bitvec_setWidth_shift_toNat (show 12 + 180 ≤ 192 by trivial),
      ←BitVec.toNat_and,
      ←BitVec.toNat_xor,
      ←bitvec_setWidth_toNat (width1 := 180) (width2 := 192) (h_width := by trivial),
      ←BitVec.toNat_add_of_lt
    ]
    . congr 1
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt h_x0,
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
        Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        ←Nat.shiftLeft_and_distrib,
        ←Nat.shiftLeft_xor_distrib
      ]
      have : x3 ^^^ x4 &&& x5 < 1532495540865888858358347027150309183618739122183602176 := by
        apply Nat.xor_lt_two_pow (n := 180)
        . omega
        . have := Nat.and_le_right (n := x4) (m := x5)
          omega
      have : x0 ^^^ x1 &&& x2 < 4096 := by
        apply Nat.xor_lt_two_pow (n := 12)
        . omega
        . have := Nat.and_le_right (n := x1) (m := x2)
          omega
      omega

  lemma separate_decodes_step_15_lt :
    Normalize.normalize_unpacked x1 4 <<< 168 +
    (Normalize.normalize_unpacked x2 4 <<< 156 +
    (Normalize.normalize_unpacked x3 4 <<< 144 +
    (Normalize.normalize_unpacked x4 4 <<< 132 +
    (Normalize.normalize_unpacked x5 4 <<< 120 +
    (Normalize.normalize_unpacked x6 4 <<< 108 +
    (Normalize.normalize_unpacked x7 4 <<< 96 +
    (Normalize.normalize_unpacked x8 4 <<< 84 +
    (Normalize.normalize_unpacked x9 4 <<< 72 +
    (Normalize.normalize_unpacked x10 4 <<< 60 +
    (Normalize.normalize_unpacked x11 4 <<< 48 +
    (Normalize.normalize_unpacked x12 4 <<< 36 +
    (Normalize.normalize_unpacked x13 4 <<< 24 +
    (Normalize.normalize_unpacked x14 4 <<< 12 +
    Normalize.normalize_unpacked x15 4))))))))))))) < 2^180
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    have := Normalize.normalize_unpacked_4_le (x := x13)
    have := Normalize.normalize_unpacked_4_le (x := x14)
    have := Normalize.normalize_unpacked_4_le (x := x15)
    omega

  syntax "rho_aux" ident : tactic
  macro_rules
    | `(tactic| rho_aux $P:ident) => `(
    tactic| (
      have : $P ≥ 1756 := by omega
      simp [to_cell_manager, *, normalize_rho]
      rw [Nat.mod_eq_of_lt]
      exact lt_of_le_of_lt
        Normalize.normalize_unpacked_4_le
        (by omega)
    )
  )

  set_option maxHeartbeats 0
  example {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2690186458022863184501052609946142749758152333341729076955<P):
    os' c round 0 0
    = sorry
  := by
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round' := Finset.mem_Icc.mp h_round
    have h_P': P ≥ 4096 := by omega
    simp [os', keccak_constants, list_ops, rho_pi_chi_cells, cell_manager_to_raw]
    have : 12 * round % c.n = 12 * round := by rw [Nat.mod_eq_of_lt (by omega)]
    have h_to_cell_manager: 12 * round + 11 < c.n := by omega
    have h_normalize_rho_0_0 : (c.get_advice 70 (12 * round % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 (12 * round % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_0 : (c.get_advice 71 (12 * round % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 (12 * round % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_0 : (c.get_advice 72 (12 * round % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 (12 * round % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_1 : (c.get_advice 70 ((12 * round + 1) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 1) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_1 : (c.get_advice 71 ((12 * round + 1) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 1) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_1 : (c.get_advice 72 ((12 * round + 1) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 1) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_2 : (c.get_advice 70 ((12 * round + 2) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 2) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_2 : (c.get_advice 71 ((12 * round + 2) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 2) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_2 : (c.get_advice 72 ((12 * round + 2) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 2) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_3 : (c.get_advice 70 ((12 * round + 3) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 3) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_3 : (c.get_advice 71 ((12 * round + 3) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 3) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_3 : (c.get_advice 72 ((12 * round + 3) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 3) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_4 : (c.get_advice 70 ((12 * round + 4) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 4) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_4 : (c.get_advice 71 ((12 * round + 4) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 4) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_4 : (c.get_advice 72 ((12 * round + 4) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 4) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_5 : (c.get_advice 70 ((12 * round + 5) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 5) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_5 : (c.get_advice 71 ((12 * round + 5) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 5) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_5 : (c.get_advice 72 ((12 * round + 5) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 5) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_6 : (c.get_advice 70 ((12 * round + 6) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 6) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_6 : (c.get_advice 71 ((12 * round + 6) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 6) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_6 : (c.get_advice 72 ((12 * round + 6) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 6) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_7 : (c.get_advice 70 ((12 * round + 7) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 7) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_7 : (c.get_advice 71 ((12 * round + 7) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 7) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_7 : (c.get_advice 72 ((12 * round + 7) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 7) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_8 : (c.get_advice 70 ((12 * round + 8) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 8) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_8 : (c.get_advice 71 ((12 * round + 8) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 8) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_8 : (c.get_advice 72 ((12 * round + 8) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 8) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_9 : (c.get_advice 70 ((12 * round + 9) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 9) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_9 : (c.get_advice 71 ((12 * round + 9) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 9) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_9 : (c.get_advice 72 ((12 * round + 9) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 9) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_10 : (c.get_advice 70 ((12 * round + 10) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 10) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_10 : (c.get_advice 71 ((12 * round + 10) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 10) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_10 : (c.get_advice 72 ((12 * round + 10) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 10) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_11 : (c.get_advice 70 ((12 * round + 11) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12 * round + 11) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_11 : (c.get_advice 71 ((12 * round + 11) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 11) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_11 : (c.get_advice 72 ((12 * round + 11) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12 * round + 11) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_12 : (c.get_advice 75 (12 * round % c.n)).val = Normalize.normalize_unpacked (c.get_advice 40 (12 * round % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_12 : (c.get_advice 76 (12 * round % c.n)).val = Normalize.normalize_unpacked (c.get_advice 41 (12 * round % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_12 : (c.get_advice 77 (12 * round % c.n)).val = Normalize.normalize_unpacked (c.get_advice 42 (12 * round % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_13 : (c.get_advice 75 ((12 * round + 1) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 40 ((12 * round + 1) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_13 : (c.get_advice 76 ((12 * round + 1) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 41 ((12 * round + 1) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_13 : (c.get_advice 77 ((12 * round + 1) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 42 ((12 * round + 1) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_14 : (c.get_advice 75 ((12 * round + 2) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 40 ((12 * round + 2) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_14 : (c.get_advice 76 ((12 * round + 2) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 41 ((12 * round + 2) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_14 : (c.get_advice 77 ((12 * round + 2) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 42 ((12 * round + 2) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_0_15 : (c.get_advice 75 ((12 * round + 3) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 40 ((12 * round + 3) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_1_15 : (c.get_advice 76 ((12 * round + 3) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 41 ((12 * round + 3) % c.n)).val 4 := by rho_aux P
    have h_normalize_rho_2_15 : (c.get_advice 77 ((12 * round + 3) % c.n)).val = Normalize.normalize_unpacked (c.get_advice 42 ((12 * round + 3) % c.n)).val 4 := by rho_aux P
    rewrite [
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by omega) h_normalize_rho_0_0 h_normalize_rho_1_0 h_normalize_rho_2_0,
      h_normalize_rho_0_0, h_normalize_rho_1_0, h_normalize_rho_2_0,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_1 h_normalize_rho_1_1 h_normalize_rho_2_1,
      h_normalize_rho_0_1, h_normalize_rho_1_1, h_normalize_rho_2_1,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_2 h_normalize_rho_1_2 h_normalize_rho_2_2,
      h_normalize_rho_0_2, h_normalize_rho_1_2, h_normalize_rho_2_2,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_3 h_normalize_rho_1_3 h_normalize_rho_2_3,
      h_normalize_rho_0_3, h_normalize_rho_1_3, h_normalize_rho_2_3,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_4 h_normalize_rho_1_4 h_normalize_rho_2_4,
      h_normalize_rho_0_4, h_normalize_rho_1_4, h_normalize_rho_2_4,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_5 h_normalize_rho_1_5 h_normalize_rho_2_5,
      h_normalize_rho_0_5, h_normalize_rho_1_5, h_normalize_rho_2_5,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_6 h_normalize_rho_1_6 h_normalize_rho_2_6,
      h_normalize_rho_0_6, h_normalize_rho_1_6, h_normalize_rho_2_6,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_7 h_normalize_rho_1_7 h_normalize_rho_2_7,
      h_normalize_rho_0_7, h_normalize_rho_1_7, h_normalize_rho_2_7,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_8 h_normalize_rho_1_8 h_normalize_rho_2_8,
      h_normalize_rho_0_8, h_normalize_rho_1_8, h_normalize_rho_2_8,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_9 h_normalize_rho_1_9 h_normalize_rho_2_9,
      h_normalize_rho_0_9, h_normalize_rho_1_9, h_normalize_rho_2_9,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_10 h_normalize_rho_1_10 h_normalize_rho_2_10,
      h_normalize_rho_0_10, h_normalize_rho_1_10, h_normalize_rho_2_10,
      chi_base_0_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_11 h_normalize_rho_1_11 h_normalize_rho_2_11,
      h_normalize_rho_0_11, h_normalize_rho_1_11, h_normalize_rho_2_11,
      chi_base_1_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_12 h_normalize_rho_1_12 h_normalize_rho_2_12,
      h_normalize_rho_0_12, h_normalize_rho_1_12, h_normalize_rho_2_12,
      chi_base_1_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_13 h_normalize_rho_1_13 h_normalize_rho_2_13,
      h_normalize_rho_0_13, h_normalize_rho_1_13, h_normalize_rho_2_13,
      chi_base_1_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_14 h_normalize_rho_1_14 h_normalize_rho_2_14,
      h_normalize_rho_0_14, h_normalize_rho_1_14, h_normalize_rho_2_14,
      chi_base_1_0 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega) h_normalize_rho_0_15 h_normalize_rho_1_15 h_normalize_rho_2_15,
      h_normalize_rho_0_15, h_normalize_rho_1_15, h_normalize_rho_2_15,
    ]
    simp [Decode.expr.eq_def, keccak_constants, mul_add, ←mul_assoc, ←pow_add]
    simp only [zmod_pow_shift_simps, add_assoc, ←Nat.cast_add]
    rewrite [
      mul_comm (2^12), ←Nat.shiftLeft_eq,
      mul_comm (2^24), ←Nat.shiftLeft_eq,
      mul_comm (2^36), ←Nat.shiftLeft_eq,
      mul_comm (2^48), ←Nat.shiftLeft_eq,
      mul_comm (2^60), ←Nat.shiftLeft_eq,
      mul_comm (2^72), ←Nat.shiftLeft_eq,
      mul_comm (2^84), ←Nat.shiftLeft_eq,
      mul_comm (2^96), ←Nat.shiftLeft_eq,
      mul_comm (2^108), ←Nat.shiftLeft_eq,
      mul_comm (2^120), ←Nat.shiftLeft_eq,
      mul_comm (2^132), ←Nat.shiftLeft_eq,
      mul_comm (2^144), ←Nat.shiftLeft_eq,
      mul_comm (2^156), ←Nat.shiftLeft_eq,
      mul_comm (2^168), ←Nat.shiftLeft_eq,
      mul_comm (2^180), ←Nat.shiftLeft_eq,
    ]
    simp only [
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Nat.shiftLeft_xor_distrib,
      Nat.shiftLeft_and_distrib,
    ]
    rewrite [
      separate_decodes_step_1
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial)),
      separate_decodes_step_2
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_2_lt
        separate_decodes_step_2_lt
        separate_decodes_step_2_lt,
      separate_decodes_step_3
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_3_lt
        separate_decodes_step_3_lt
        separate_decodes_step_3_lt,
      separate_decodes_step_4
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_4_lt
        separate_decodes_step_4_lt
        separate_decodes_step_4_lt,
      separate_decodes_step_5
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_5_lt
        separate_decodes_step_5_lt
        separate_decodes_step_5_lt,
      separate_decodes_step_6
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_6_lt
        separate_decodes_step_6_lt
        separate_decodes_step_6_lt,
      separate_decodes_step_7
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_7_lt
        separate_decodes_step_7_lt
        separate_decodes_step_7_lt,
      separate_decodes_step_8
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_8_lt
        separate_decodes_step_8_lt
        separate_decodes_step_8_lt,
      separate_decodes_step_9
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_9_lt
        separate_decodes_step_9_lt
        separate_decodes_step_9_lt,
      separate_decodes_step_10
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_10_lt
        separate_decodes_step_10_lt
        separate_decodes_step_10_lt,
      separate_decodes_step_11
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_11_lt
        separate_decodes_step_11_lt
        separate_decodes_step_11_lt,
      separate_decodes_step_12
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_12_lt
        separate_decodes_step_12_lt
        separate_decodes_step_12_lt,
      separate_decodes_step_13
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_13_lt
        separate_decodes_step_13_lt
        separate_decodes_step_13_lt,
      separate_decodes_step_14
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_14_lt
        separate_decodes_step_14_lt
        separate_decodes_step_14_lt,
      separate_decodes_step_15
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_decodes_step_15_lt
        separate_decodes_step_15_lt
        separate_decodes_step_15_lt,
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 41 ((12 * round + 3) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 41 ((12 * round + 2) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 41 ((12 * round + 1) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 41 (12 * round  % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 11) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 10) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 9) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 8) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 7) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 6) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 5) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 4) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 3) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 2) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 ((12 * round + 1) % c.n)).val 4),
      ←bit_invert_to_bitvec (x := Normalize.normalize_unpacked (c.get_advice 36 (12 * round  % c.n)).val 4),
    ]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat (x := (c.get_advice _ _).val) (show 12 = BIT_COUNT*4 by simp [keccak_constants])
    ]
    rewrite [
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    simp [to_cell_manager, h_to_cell_manager]
    have h_cell_336 := (cell_336_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_337 := (cell_337_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_338 := (cell_338_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_339 := (cell_339_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_340 := (cell_340_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_341 := (cell_341_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_342 := (cell_342_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_343 := (cell_343_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_344 := (cell_344_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_345 := (cell_345_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_346 := (cell_346_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_347 := (cell_347_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_396 := (cell_396_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_397 := (cell_397_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_398 := (cell_398_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_399 := (cell_399_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_336 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_337 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_337 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_338 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_338 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_339 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_339 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_340 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_340 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_341 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_341 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_342 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_342 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_343 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_343 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_344 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_344 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_345 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_345 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_346 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_346 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_347 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_347 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_396 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_396 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_397 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_397 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_398 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_398 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_399 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_399 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega),
    ]
    have :
      Normalize.normalize_unpacked (os c round 0 0).val 64 =
      Normalize.normalize_unpacked
        ((cell_manager c round 399).val <<< 180 +
          ((cell_manager c round 398).val <<< 168 +
            ((cell_manager c round 397).val <<< 156 +
              ((cell_manager c round 396).val <<< 144 +
                ((cell_manager c round 347).val <<< 132 +
                  ((cell_manager c round 346).val <<< 120 +
                    ((cell_manager c round 345).val <<< 108 +
                      ((cell_manager c round 344).val <<< 96 +
                        ((cell_manager c round 343).val <<< 84 +
                          ((cell_manager c round 342).val <<< 72 +
                            ((cell_manager c round 341).val <<< 60 +
                              ((cell_manager c round 340).val <<< 48 +
                                ((cell_manager c round 339).val <<< 36 +
                                  ((cell_manager c round 338).val <<< 24 +
                                    ((cell_manager c round 337).val <<< 12 +
                                      (cell_manager c round 336).val)))))))))))))))
        64
    := by
      rewrite [←s_input_parts_0_0 h_meets_constraints h_round]
      simp [
        Decode.expr.eq_def, keccak_constants,
        mul_add, ←mul_assoc, ←pow_add,
        ZMod.val_add, ZMod.val_mul
      ]
      have one_lt_p: Fact (1 < P) := by constructor; omega
      have h_2pow12: ((2: ZMod P)^12).val = 2^12 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow24: ((2: ZMod P)^24).val = 2^24 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow36: ((2: ZMod P)^36).val = 2^36 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow48: ((2: ZMod P)^48).val = 2^48 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow60: ((2: ZMod P)^60).val = 2^60 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow72: ((2: ZMod P)^72).val = 2^72 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow84: ((2: ZMod P)^84).val = 2^84 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow96: ((2: ZMod P)^96).val = 2^96 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow108: ((2: ZMod P)^108).val = 2^108 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow120: ((2: ZMod P)^120).val = 2^120 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow132: ((2: ZMod P)^132).val = 2^132 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow144: ((2: ZMod P)^144).val = 2^144 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow156: ((2: ZMod P)^156).val = 2^156 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow168: ((2: ZMod P)^168).val = 2^168 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow180: ((2: ZMod P)^180).val = 2^180 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [
        h_2pow12,
        h_2pow24,
        h_2pow36,
        h_2pow48,
        h_2pow60,
        h_2pow72,
        h_2pow84,
        h_2pow96,
        h_2pow108,
        h_2pow120,
        h_2pow132,
        h_2pow144,
        h_2pow156,
        h_2pow168,
        h_2pow180,
      ]
      simp only [mul_comm (2^_), ←Nat.shiftLeft_eq]
      rewrite [Nat.mod_eq_of_lt (by omega)]
      simp [←Nat.add_assoc]
    rewrite [←this]

    . sorry
    -- have ⟨h_input_parts, h_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 0
    -- simp [
    --   keccak_constants, list_ops, word_parts_known,
    --   get_rotate_count, s_parts_cell_offsets.eq_def, pi_region_start.eq_def,
    --   target_part_sizes_known,
    --   SplitUniform.input_parts.eq_def,
    --   rho_pi_chi_cells,
    -- ] at h_input_parts

    -- have : Normalize.normalize_unpacked
    --       x0.val ^^^
    --         bit_invert (c.get_advice 76 ((12 * round + 3) % c.n)).val 4 &&&
    --           (c.get_advice 77 ((12 * round + 3) % c.n)).val)
    --       4
    -- simp only [
    --   Normalize.normalize_unpacked_xor,
    --   show
    --   Normalize.normalize_unpacked_and,

    -- ]


  -- example :
  --   (s_parts' c round 0 0).1 = sorry
  -- := by
  --   simp [
  --     s_parts', TransformTo.expr, keccak_constants, word_parts_known, list_ops,
  --     s_parts, SplitUniform.expr, SplitUniform.expr_res, target_part_sizes_known,
  --     SplitUniform.output_parts, rho_pi_chi_cells, fin_vals
  --   ]


  -- lemma s_input_parts_0_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
  --   Decode.expr [
  --     (4, c.get_advice 56 (12 * round + 9)),
  --     (4, c.get_advice 56 (12 * round + 10)),
  --     (4, c.get_advice 56 (12 * round + 11)),
  --     (4, c.get_advice 61 (12 * round)),
  --     (4, c.get_advice 61 (12 * round + 1)),
  --     (4, c.get_advice 61 (12 * round + 2)),
  --     (4, c.get_advice 61 (12 * round + 3)),
  --     (4, c.get_advice 56 (12 * round)),
  --     (4, c.get_advice 56 (12 * round + 1)),
  --     (4, c.get_advice 56 (12 * round + 2)),
  --     (4, c.get_advice 56 (12 * round + 3)),
  --     (4, c.get_advice 56 (12 * round + 4)),
  --     (4, c.get_advice 56 (12 * round + 5)),
  --     (4, c.get_advice 56 (12 * round + 6)),
  --     (4, c.get_advice 56 (12 * round + 7)),
  --     (4, c.get_advice 56 (12 * round + 8))
  --   ] =
  --   os c round 0 1
  -- := by
  --   have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 1
  --   have h_n := n_range_of_meets_constraints h_meets_constraints
  --   simp [
  --     keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
  --     s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_location,
  --     rho_pi_chi_row, rho_pi_chi_column, fin_vals, List.rotateLeft
  --   ] at h_s_input_parts
  --   replace h_round := Finset.mem_Icc.mp h_round
  --   rewrite [
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega)
  --   ] at h_s_input_parts
  --   exact h_s_input_parts

  -- lemma s_input_parts_0_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
  --   Decode.expr [
  --     (1, c.get_advice 140 (12 * round + 11)),
  --     (4, c.get_advice 42 (12 * round + 5)),
  --     (4, c.get_advice 42 (12 * round + 6)),
  --     (4, c.get_advice 42 (12 * round + 7)),
  --     (4, c.get_advice 42 (12 * round + 8)),
  --     (4, c.get_advice 42 (12 * round + 9)),
  --     (4, c.get_advice 42 (12 * round + 10)),
  --     (4, c.get_advice 42 (12 * round + 11)),
  --     (4, c.get_advice 47 (12 * round)),
  --     (4, c.get_advice 47 (12 * round + 1)),
  --     (4, c.get_advice 47 (12 * round + 2)),
  --     (4, c.get_advice 47 (12 * round + 3)),
  --     (4, c.get_advice 47 (12 * round + 4)),
  --     (4, c.get_advice 47 (12 * round + 5)),
  --     (4, c.get_advice 47 (12 * round + 6)),
  --     (4, c.get_advice 47 (12 * round + 7)),
  --     (3, c.get_advice 140 (12 * round + 10))
  --   ] =
  --   os c round 0 2
  -- := by
  --   have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 2
  --   have h_n := n_range_of_meets_constraints h_meets_constraints
  --   simp [
  --     keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
  --     s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_location,
  --     rho_pi_chi_row, rho_pi_chi_column, fin_vals, List.rotateLeft, cell_manager_to_raw
  --   ] at h_s_input_parts
  --   replace h_round := Finset.mem_Icc.mp h_round
  --   rewrite [
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega)
  --   ] at h_s_input_parts
  --   exact h_s_input_parts

  -- lemma s_rot_parts_0_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
  --   c.get_advice 140 (12 * round + 10) + c.get_advice 140 (12 * round + 11) * 2 ^ 9 =
  --   c.get_advice 42 (12 * round + 4)
  -- := by
  --   have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 2
  --   have h_n := n_range_of_meets_constraints h_meets_constraints
  --   simp [
  --     keccak_constants, fin_vals, list_ops,
  --     word_parts_known, get_rotate_count, target_part_sizes_known,
  --     SplitUniform.rot_parts.eq_def, s_parts_cell_offsets.eq_def,
  --     pi_region_start.eq_def, rho_pi_chi_location,
  --     rho_pi_chi_row, rho_pi_chi_column, cell_manager_to_raw
  --   ] at h_s_rot_parts
  --   replace h_round := Finset.mem_Icc.mp h_round
  --   rewrite [
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega),
  --     Nat.mod_eq_of_lt (by omega)
  --   ] at h_s_rot_parts
  --   exact h_s_rot_parts

  -- lemma s_parts'_eq_rho {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
  --   (s_parts' c round 0 0).1 =
  --   sorry
  -- := by
  --   have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 0
  --   simp [
  --     keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
  --     s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts
  --   ] at h_s_input_parts
  --   have h_s_parts' := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
  --   unfold s_parts'

end Keccak.Soundness

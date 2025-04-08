import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.NormalizeRho.All
import Examples.Scroll.Keccak.Soundness.RotPartRanges.All
import Examples.Scroll.Keccak.Soundness.RhoRange.All
import Examples.Scroll.Keccak.Soundness.RhoState
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi

namespace Keccak.Soundness
  lemma rho_s_0_0_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_0_0 c round = ((BitVec.ofNat 192 (os c round 0 0).val).rotateLeft (BIT_COUNT * RHO_MATRIX 0 0)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts
    ] at h_s_rot_parts
    unfold rho_s_0_0
    rewrite [←h_s_input_parts]
    have rotate_zero (bv: BitVec 192): bv.rotateLeft 0 = bv := by bv_decide
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      zmod_pow_simps, zmod_val_ofNat_of_lt (show 4096 < P by omega),
      nat_shiftLeft_eq_mul_comm, add_assoc, rotate_zero
    ]
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
    rw [Nat.mod_eq_of_lt (b := P), Nat.mod_eq_of_lt] <;> omega

  lemma rho_s_0_1_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_0_1 c round = ((BitVec.ofNat 192 (os c round 0 1).val).rotateLeft (BIT_COUNT * RHO_MATRIX 0 1)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def
    ] at h_s_rot_parts
    unfold rho_s_0_1
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 4096 < P by omega), add_assoc, -BitVec.toNat_rotateLeft
    ]
    have h_cell_0 := (cell_588_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_589_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_590_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_591_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_592_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_593_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_594_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_595_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_596_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_597_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_598_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_599_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_648_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_649_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_650_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_651_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_12 (n) := nat_shiftLeft_eq_mul_comm (m := 12) (n := n)
    have h_shift_24 (n) := nat_shiftLeft_eq_mul_comm (m := 24) (n := n)
    have h_shift_36 (n) := nat_shiftLeft_eq_mul_comm (m := 36) (n := n)
    have h_shift_48 (n) := nat_shiftLeft_eq_mul_comm (m := 48) (n := n)
    have h_shift_60 (n) := nat_shiftLeft_eq_mul_comm (m := 60) (n := n)
    have h_shift_72 (n) := nat_shiftLeft_eq_mul_comm (m := 72) (n := n)
    have h_shift_84 (n) := nat_shiftLeft_eq_mul_comm (m := 84) (n := n)
    have h_shift_96 (n) := nat_shiftLeft_eq_mul_comm (m := 96) (n := n)
    have h_shift_108 (n) := nat_shiftLeft_eq_mul_comm (m := 108) (n := n)
    have h_shift_120 (n) := nat_shiftLeft_eq_mul_comm (m := 120) (n := n)
    have h_shift_132 (n) := nat_shiftLeft_eq_mul_comm (m := 132) (n := n)
    have h_shift_144 (n) := nat_shiftLeft_eq_mul_comm (m := 144) (n := n)
    have h_shift_156 (n) := nat_shiftLeft_eq_mul_comm (m := 156) (n := n)
    have h_shift_168 (n) := nat_shiftLeft_eq_mul_comm (m := 168) (n := n)
    have h_shift_180 (n) := nat_shiftLeft_eq_mul_comm (m := 180) (n := n)
    simp at h_shift_12 h_shift_24 h_shift_36 h_shift_48 h_shift_60 h_shift_72 h_shift_84 h_shift_96 h_shift_108 h_shift_120 h_shift_132 h_shift_144 h_shift_156 h_shift_168 h_shift_180
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      h_bitvec h_cell_15,
      ←h_shift_12,
      ←h_shift_24,
      ←h_shift_36,
      ←h_shift_48,
      ←h_shift_60,
      ←h_shift_72,
      ←h_shift_84,
      ←h_shift_96,
      ←h_shift_108,
      ←h_shift_120,
      ←h_shift_132,
      ←h_shift_144,
      ←h_shift_156,
      ←h_shift_168,
      ←h_shift_180,
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_0_2_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P):
    rho_s_0_2 c round = ((BitVec.ofNat 192 (os c round 0 2).val).rotateLeft (BIT_COUNT * RHO_MATRIX 0 2)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_0_2
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_425_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_426_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_427_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_428_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_429_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_430_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_431_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_480_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_481_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_482_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_483_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_484_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_485_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_486_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_487_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_3 (n) := nat_shiftLeft_eq_mul_comm (m := 3) (n := n)
    have h_shift_15 (n) := nat_shiftLeft_eq_mul_comm (m := 15) (n := n)
    have h_shift_27 (n) := nat_shiftLeft_eq_mul_comm (m := 27) (n := n)
    have h_shift_39 (n) := nat_shiftLeft_eq_mul_comm (m := 39) (n := n)
    have h_shift_51 (n) := nat_shiftLeft_eq_mul_comm (m := 51) (n := n)
    have h_shift_63 (n) := nat_shiftLeft_eq_mul_comm (m := 63) (n := n)
    have h_shift_75 (n) := nat_shiftLeft_eq_mul_comm (m := 75) (n := n)
    have h_shift_87 (n) := nat_shiftLeft_eq_mul_comm (m := 87) (n := n)
    have h_shift_99 (n) := nat_shiftLeft_eq_mul_comm (m := 99) (n := n)
    have h_shift_111 (n) := nat_shiftLeft_eq_mul_comm (m := 111) (n := n)
    have h_shift_123 (n) := nat_shiftLeft_eq_mul_comm (m := 123) (n := n)
    have h_shift_135 (n) := nat_shiftLeft_eq_mul_comm (m := 135) (n := n)
    have h_shift_147 (n) := nat_shiftLeft_eq_mul_comm (m := 147) (n := n)
    have h_shift_159 (n) := nat_shiftLeft_eq_mul_comm (m := 159) (n := n)
    have h_shift_171 (n) := nat_shiftLeft_eq_mul_comm (m := 171) (n := n)
    have h_shift_183 (n) := nat_shiftLeft_eq_mul_comm (m := 183) (n := n)
    simp at h_shift_3 h_shift_15 h_shift_27 h_shift_39 h_shift_51 h_shift_63 h_shift_75 h_shift_87 h_shift_99 h_shift_111 h_shift_123 h_shift_135 h_shift_147 h_shift_159 h_shift_171 h_shift_183
    have h_rot_base := cell_1607_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1606_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_3,
      ←Nat.shiftLeft_eq (b := 9),
      ←h_shift_15,
      ←h_shift_27,
      ←h_shift_39,
      ←h_shift_51,
      ←h_shift_63,
      ←h_shift_75,
      ←h_shift_87,
      ←h_shift_99,
      ←h_shift_111,
      ←h_shift_123,
      ←h_shift_135,
      ←h_shift_147,
      ←h_shift_159,
      ←h_shift_171,
      ←h_shift_183,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 15 (h := by trivial),
      bitvec_toNat_shift_add 27 (h := by trivial),
      bitvec_toNat_shift_add 39 (h := by trivial),
      bitvec_toNat_shift_add 51 (h := by trivial),
      bitvec_toNat_shift_add 63 (h := by trivial),
      bitvec_toNat_shift_add 75 (h := by trivial),
      bitvec_toNat_shift_add 87 (h := by trivial),
      bitvec_toNat_shift_add 99 (h := by trivial),
      bitvec_toNat_shift_add 111 (h := by trivial),
      bitvec_toNat_shift_add 123 (h := by trivial),
      bitvec_toNat_shift_add 135 (h := by trivial),
      bitvec_toNat_shift_add 147 (h := by trivial),
      bitvec_toNat_shift_add 159 (h := by trivial),
      bitvec_toNat_shift_add 171 (h := by trivial),
      bitvec_toNat_shift_add 183 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_0_3_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_0_3 c round = ((BitVec.ofNat 192 (os c round 0 3).val).rotateLeft (BIT_COUNT * RHO_MATRIX 0 3)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_0_3
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_676_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_677_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_678_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_679_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_680_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_681_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_682_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_683_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_732_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_733_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_735_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_736_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_737_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_738_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_739_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_9 (n) := nat_shiftLeft_eq_mul_comm (m := 9) (n := n)
    have h_shift_21 (n) := nat_shiftLeft_eq_mul_comm (m := 21) (n := n)
    have h_shift_33 (n) := nat_shiftLeft_eq_mul_comm (m := 33) (n := n)
    have h_shift_45 (n) := nat_shiftLeft_eq_mul_comm (m := 45) (n := n)
    have h_shift_57 (n) := nat_shiftLeft_eq_mul_comm (m := 57) (n := n)
    have h_shift_69 (n) := nat_shiftLeft_eq_mul_comm (m := 69) (n := n)
    have h_shift_81 (n) := nat_shiftLeft_eq_mul_comm (m := 81) (n := n)
    have h_shift_93 (n) := nat_shiftLeft_eq_mul_comm (m := 93) (n := n)
    have h_shift_105 (n) := nat_shiftLeft_eq_mul_comm (m := 105) (n := n)
    have h_shift_117 (n) := nat_shiftLeft_eq_mul_comm (m := 117) (n := n)
    have h_shift_129 (n) := nat_shiftLeft_eq_mul_comm (m := 129) (n := n)
    have h_shift_141 (n) := nat_shiftLeft_eq_mul_comm (m := 141) (n := n)
    have h_shift_153 (n) := nat_shiftLeft_eq_mul_comm (m := 153) (n := n)
    have h_shift_165 (n) := nat_shiftLeft_eq_mul_comm (m := 165) (n := n)
    have h_shift_177 (n) := nat_shiftLeft_eq_mul_comm (m := 177) (n := n)
    have h_shift_189 (n) := nat_shiftLeft_eq_mul_comm (m := 189) (n := n)
    simp at h_shift_9 h_shift_21 h_shift_33 h_shift_45 h_shift_57 h_shift_69 h_shift_81 h_shift_93 h_shift_105 h_shift_117 h_shift_129 h_shift_141 h_shift_153 h_shift_165 h_shift_177 h_shift_189
    have h_rot_base := cell_1616_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1617_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_9,
      ←Nat.shiftLeft_eq (b := 3),
      ←h_shift_21,
      ←h_shift_33,
      ←h_shift_45,
      ←h_shift_57,
      ←h_shift_69,
      ←h_shift_81,
      ←h_shift_93,
      ←h_shift_105,
      ←h_shift_117,
      ←h_shift_129,
      ←h_shift_141,
      ←h_shift_153,
      ←h_shift_165,
      ←h_shift_177,
      ←h_shift_189,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 21 (h := by trivial),
      bitvec_toNat_shift_add 33 (h := by trivial),
      bitvec_toNat_shift_add 45 (h := by trivial),
      bitvec_toNat_shift_add 57 (h := by trivial),
      bitvec_toNat_shift_add 69 (h := by trivial),
      bitvec_toNat_shift_add 81 (h := by trivial),
      bitvec_toNat_shift_add 93 (h := by trivial),
      bitvec_toNat_shift_add 105 (h := by trivial),
      bitvec_toNat_shift_add 117 (h := by trivial),
      bitvec_toNat_shift_add 129 (h := by trivial),
      bitvec_toNat_shift_add 141 (h := by trivial),
      bitvec_toNat_shift_add 153 (h := by trivial),
      bitvec_toNat_shift_add 165 (h := by trivial),
      bitvec_toNat_shift_add 177 (h := by trivial),
      bitvec_toNat_shift_add 189 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_0_4_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_0_4 c round = ((BitVec.ofNat 192 (os c round 0 4).val).rotateLeft (BIT_COUNT * RHO_MATRIX 0 4)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_0_4
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_512_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_513_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_514_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_515_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_565_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_566_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_567_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_568_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_569_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_570_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_571_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_572_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_573_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_574_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_575_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_6 (n) := nat_shiftLeft_eq_mul_comm (m := 6) (n := n)
    have h_shift_18 (n) := nat_shiftLeft_eq_mul_comm (m := 18) (n := n)
    have h_shift_30 (n) := nat_shiftLeft_eq_mul_comm (m := 30) (n := n)
    have h_shift_42 (n) := nat_shiftLeft_eq_mul_comm (m := 42) (n := n)
    have h_shift_54 (n) := nat_shiftLeft_eq_mul_comm (m := 54) (n := n)
    have h_shift_66 (n) := nat_shiftLeft_eq_mul_comm (m := 66) (n := n)
    have h_shift_78 (n) := nat_shiftLeft_eq_mul_comm (m := 78) (n := n)
    have h_shift_90 (n) := nat_shiftLeft_eq_mul_comm (m := 90) (n := n)
    have h_shift_102 (n) := nat_shiftLeft_eq_mul_comm (m := 102) (n := n)
    have h_shift_114 (n) := nat_shiftLeft_eq_mul_comm (m := 114) (n := n)
    have h_shift_126 (n) := nat_shiftLeft_eq_mul_comm (m := 126) (n := n)
    have h_shift_138 (n) := nat_shiftLeft_eq_mul_comm (m := 138) (n := n)
    have h_shift_150 (n) := nat_shiftLeft_eq_mul_comm (m := 150) (n := n)
    have h_shift_162 (n) := nat_shiftLeft_eq_mul_comm (m := 162) (n := n)
    have h_shift_174 (n) := nat_shiftLeft_eq_mul_comm (m := 174) (n := n)
    have h_shift_186 (n) := nat_shiftLeft_eq_mul_comm (m := 186) (n := n)
    simp at h_shift_6 h_shift_18 h_shift_30 h_shift_42 h_shift_54 h_shift_66 h_shift_78 h_shift_90 h_shift_102 h_shift_114 h_shift_126 h_shift_138 h_shift_150 h_shift_162 h_shift_174 h_shift_186
    have h_rot_base := cell_1624_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1625_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_6,
      ←Nat.shiftLeft_eq (b := 6),
      ←h_shift_18,
      ←h_shift_30,
      ←h_shift_42,
      ←h_shift_54,
      ←h_shift_66,
      ←h_shift_78,
      ←h_shift_90,
      ←h_shift_102,
      ←h_shift_114,
      ←h_shift_126,
      ←h_shift_138,
      ←h_shift_150,
      ←h_shift_162,
      ←h_shift_174,
      ←h_shift_186,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 18 (h := by trivial),
      bitvec_toNat_shift_add 30 (h := by trivial),
      bitvec_toNat_shift_add 42 (h := by trivial),
      bitvec_toNat_shift_add 54 (h := by trivial),
      bitvec_toNat_shift_add 66 (h := by trivial),
      bitvec_toNat_shift_add 78 (h := by trivial),
      bitvec_toNat_shift_add 90 (h := by trivial),
      bitvec_toNat_shift_add 102 (h := by trivial),
      bitvec_toNat_shift_add 114 (h := by trivial),
      bitvec_toNat_shift_add 126 (h := by trivial),
      bitvec_toNat_shift_add 138 (h := by trivial),
      bitvec_toNat_shift_add 150 (h := by trivial),
      bitvec_toNat_shift_add 162 (h := by trivial),
      bitvec_toNat_shift_add 174 (h := by trivial),
      bitvec_toNat_shift_add 186 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_1_0_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_1_0 c round = ((BitVec.ofNat 192 (os c round 1 0).val).rotateLeft (BIT_COUNT * RHO_MATRIX 1 0)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_1_0
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_465_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_466_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_467_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_516_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_517_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_518_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_519_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_520_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_521_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_522_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_523_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_524_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_525_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_526_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_527_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_9 (n) := nat_shiftLeft_eq_mul_comm (m := 9) (n := n)
    have h_shift_21 (n) := nat_shiftLeft_eq_mul_comm (m := 21) (n := n)
    have h_shift_33 (n) := nat_shiftLeft_eq_mul_comm (m := 33) (n := n)
    have h_shift_45 (n) := nat_shiftLeft_eq_mul_comm (m := 45) (n := n)
    have h_shift_57 (n) := nat_shiftLeft_eq_mul_comm (m := 57) (n := n)
    have h_shift_69 (n) := nat_shiftLeft_eq_mul_comm (m := 69) (n := n)
    have h_shift_81 (n) := nat_shiftLeft_eq_mul_comm (m := 81) (n := n)
    have h_shift_93 (n) := nat_shiftLeft_eq_mul_comm (m := 93) (n := n)
    have h_shift_105 (n) := nat_shiftLeft_eq_mul_comm (m := 105) (n := n)
    have h_shift_117 (n) := nat_shiftLeft_eq_mul_comm (m := 117) (n := n)
    have h_shift_129 (n) := nat_shiftLeft_eq_mul_comm (m := 129) (n := n)
    have h_shift_141 (n) := nat_shiftLeft_eq_mul_comm (m := 141) (n := n)
    have h_shift_153 (n) := nat_shiftLeft_eq_mul_comm (m := 153) (n := n)
    have h_shift_165 (n) := nat_shiftLeft_eq_mul_comm (m := 165) (n := n)
    have h_shift_177 (n) := nat_shiftLeft_eq_mul_comm (m := 177) (n := n)
    have h_shift_189 (n) := nat_shiftLeft_eq_mul_comm (m := 189) (n := n)
    simp at h_shift_9 h_shift_21 h_shift_33 h_shift_45 h_shift_57 h_shift_69 h_shift_81 h_shift_93 h_shift_105 h_shift_117 h_shift_129 h_shift_141 h_shift_153 h_shift_165 h_shift_177 h_shift_189
    have h_rot_base := cell_1596_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1597_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_9,
      ←Nat.shiftLeft_eq (b := 3),
      ←h_shift_21,
      ←h_shift_33,
      ←h_shift_45,
      ←h_shift_57,
      ←h_shift_69,
      ←h_shift_81,
      ←h_shift_93,
      ←h_shift_105,
      ←h_shift_117,
      ←h_shift_129,
      ←h_shift_141,
      ←h_shift_153,
      ←h_shift_165,
      ←h_shift_177,
      ←h_shift_189,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 21 (h := by trivial),
      bitvec_toNat_shift_add 33 (h := by trivial),
      bitvec_toNat_shift_add 45 (h := by trivial),
      bitvec_toNat_shift_add 57 (h := by trivial),
      bitvec_toNat_shift_add 69 (h := by trivial),
      bitvec_toNat_shift_add 81 (h := by trivial),
      bitvec_toNat_shift_add 93 (h := by trivial),
      bitvec_toNat_shift_add 105 (h := by trivial),
      bitvec_toNat_shift_add 117 (h := by trivial),
      bitvec_toNat_shift_add 129 (h := by trivial),
      bitvec_toNat_shift_add 141 (h := by trivial),
      bitvec_toNat_shift_add 153 (h := by trivial),
      bitvec_toNat_shift_add 165 (h := by trivial),
      bitvec_toNat_shift_add 177 (h := by trivial),
      bitvec_toNat_shift_add 189 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_1_1_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_1_1 c round = ((BitVec.ofNat 192 (os c round 1 1).val).rotateLeft (BIT_COUNT * RHO_MATRIX 1 1)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def
    ] at h_s_rot_parts
    unfold rho_s_1_1
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 4096 < P by omega), add_assoc, -BitVec.toNat_rotateLeft
    ]
    have h_cell_0 := (cell_348_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_349_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_350_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_351_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_352_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_353_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_354_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_355_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_356_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_357_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_358_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_359_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_408_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_409_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_410_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_411_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_12 (n) := nat_shiftLeft_eq_mul_comm (m := 12) (n := n)
    have h_shift_24 (n) := nat_shiftLeft_eq_mul_comm (m := 24) (n := n)
    have h_shift_36 (n) := nat_shiftLeft_eq_mul_comm (m := 36) (n := n)
    have h_shift_48 (n) := nat_shiftLeft_eq_mul_comm (m := 48) (n := n)
    have h_shift_60 (n) := nat_shiftLeft_eq_mul_comm (m := 60) (n := n)
    have h_shift_72 (n) := nat_shiftLeft_eq_mul_comm (m := 72) (n := n)
    have h_shift_84 (n) := nat_shiftLeft_eq_mul_comm (m := 84) (n := n)
    have h_shift_96 (n) := nat_shiftLeft_eq_mul_comm (m := 96) (n := n)
    have h_shift_108 (n) := nat_shiftLeft_eq_mul_comm (m := 108) (n := n)
    have h_shift_120 (n) := nat_shiftLeft_eq_mul_comm (m := 120) (n := n)
    have h_shift_132 (n) := nat_shiftLeft_eq_mul_comm (m := 132) (n := n)
    have h_shift_144 (n) := nat_shiftLeft_eq_mul_comm (m := 144) (n := n)
    have h_shift_156 (n) := nat_shiftLeft_eq_mul_comm (m := 156) (n := n)
    have h_shift_168 (n) := nat_shiftLeft_eq_mul_comm (m := 168) (n := n)
    have h_shift_180 (n) := nat_shiftLeft_eq_mul_comm (m := 180) (n := n)
    simp at h_shift_12 h_shift_24 h_shift_36 h_shift_48 h_shift_60 h_shift_72 h_shift_84 h_shift_96 h_shift_108 h_shift_120 h_shift_132 h_shift_144 h_shift_156 h_shift_168 h_shift_180
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      h_bitvec h_cell_15,
      ←h_shift_12,
      ←h_shift_24,
      ←h_shift_36,
      ←h_shift_48,
      ←h_shift_60,
      ←h_shift_72,
      ←h_shift_84,
      ←h_shift_96,
      ←h_shift_108,
      ←h_shift_120,
      ←h_shift_132,
      ←h_shift_144,
      ←h_shift_156,
      ←h_shift_168,
      ←h_shift_180,
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_1_2_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_1_2 c round = ((BitVec.ofNat 192 (os c round 1 2).val).rotateLeft (BIT_COUNT * RHO_MATRIX 1 2)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_1_2
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_600_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_601_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_603_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_604_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_605_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_606_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_607_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_608_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_609_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_610_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_611_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_660_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_661_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_662_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_663_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_6 (n) := nat_shiftLeft_eq_mul_comm (m := 6) (n := n)
    have h_shift_18 (n) := nat_shiftLeft_eq_mul_comm (m := 18) (n := n)
    have h_shift_30 (n) := nat_shiftLeft_eq_mul_comm (m := 30) (n := n)
    have h_shift_42 (n) := nat_shiftLeft_eq_mul_comm (m := 42) (n := n)
    have h_shift_54 (n) := nat_shiftLeft_eq_mul_comm (m := 54) (n := n)
    have h_shift_66 (n) := nat_shiftLeft_eq_mul_comm (m := 66) (n := n)
    have h_shift_78 (n) := nat_shiftLeft_eq_mul_comm (m := 78) (n := n)
    have h_shift_90 (n) := nat_shiftLeft_eq_mul_comm (m := 90) (n := n)
    have h_shift_102 (n) := nat_shiftLeft_eq_mul_comm (m := 102) (n := n)
    have h_shift_114 (n) := nat_shiftLeft_eq_mul_comm (m := 114) (n := n)
    have h_shift_126 (n) := nat_shiftLeft_eq_mul_comm (m := 126) (n := n)
    have h_shift_138 (n) := nat_shiftLeft_eq_mul_comm (m := 138) (n := n)
    have h_shift_150 (n) := nat_shiftLeft_eq_mul_comm (m := 150) (n := n)
    have h_shift_162 (n) := nat_shiftLeft_eq_mul_comm (m := 162) (n := n)
    have h_shift_174 (n) := nat_shiftLeft_eq_mul_comm (m := 174) (n := n)
    have h_shift_186 (n) := nat_shiftLeft_eq_mul_comm (m := 186) (n := n)
    simp at h_shift_6 h_shift_18 h_shift_30 h_shift_42 h_shift_54 h_shift_66 h_shift_78 h_shift_90 h_shift_102 h_shift_114 h_shift_126 h_shift_138 h_shift_150 h_shift_162 h_shift_174 h_shift_186
    have h_rot_base := cell_1608_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1609_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_6,
      ←Nat.shiftLeft_eq (b := 6),
      ←h_shift_18,
      ←h_shift_30,
      ←h_shift_42,
      ←h_shift_54,
      ←h_shift_66,
      ←h_shift_78,
      ←h_shift_90,
      ←h_shift_102,
      ←h_shift_114,
      ←h_shift_126,
      ←h_shift_138,
      ←h_shift_150,
      ←h_shift_162,
      ←h_shift_174,
      ←h_shift_186,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 18 (h := by trivial),
      bitvec_toNat_shift_add 30 (h := by trivial),
      bitvec_toNat_shift_add 42 (h := by trivial),
      bitvec_toNat_shift_add 54 (h := by trivial),
      bitvec_toNat_shift_add 66 (h := by trivial),
      bitvec_toNat_shift_add 78 (h := by trivial),
      bitvec_toNat_shift_add 90 (h := by trivial),
      bitvec_toNat_shift_add 102 (h := by trivial),
      bitvec_toNat_shift_add 114 (h := by trivial),
      bitvec_toNat_shift_add 126 (h := by trivial),
      bitvec_toNat_shift_add 138 (h := by trivial),
      bitvec_toNat_shift_add 150 (h := by trivial),
      bitvec_toNat_shift_add 162 (h := by trivial),
      bitvec_toNat_shift_add 174 (h := by trivial),
      bitvec_toNat_shift_add 186 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_1_3_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_1_3 c round = ((BitVec.ofNat 192 (os c round 1 3).val).rotateLeft (BIT_COUNT * RHO_MATRIX 1 3)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_1_3
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_436_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_437_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_438_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_439_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_440_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_441_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_442_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_443_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_492_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_493_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_494_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_496_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_497_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_498_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_499_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_9 (n) := nat_shiftLeft_eq_mul_comm (m := 9) (n := n)
    have h_shift_21 (n) := nat_shiftLeft_eq_mul_comm (m := 21) (n := n)
    have h_shift_33 (n) := nat_shiftLeft_eq_mul_comm (m := 33) (n := n)
    have h_shift_45 (n) := nat_shiftLeft_eq_mul_comm (m := 45) (n := n)
    have h_shift_57 (n) := nat_shiftLeft_eq_mul_comm (m := 57) (n := n)
    have h_shift_69 (n) := nat_shiftLeft_eq_mul_comm (m := 69) (n := n)
    have h_shift_81 (n) := nat_shiftLeft_eq_mul_comm (m := 81) (n := n)
    have h_shift_93 (n) := nat_shiftLeft_eq_mul_comm (m := 93) (n := n)
    have h_shift_105 (n) := nat_shiftLeft_eq_mul_comm (m := 105) (n := n)
    have h_shift_117 (n) := nat_shiftLeft_eq_mul_comm (m := 117) (n := n)
    have h_shift_129 (n) := nat_shiftLeft_eq_mul_comm (m := 129) (n := n)
    have h_shift_141 (n) := nat_shiftLeft_eq_mul_comm (m := 141) (n := n)
    have h_shift_153 (n) := nat_shiftLeft_eq_mul_comm (m := 153) (n := n)
    have h_shift_165 (n) := nat_shiftLeft_eq_mul_comm (m := 165) (n := n)
    have h_shift_177 (n) := nat_shiftLeft_eq_mul_comm (m := 177) (n := n)
    have h_shift_189 (n) := nat_shiftLeft_eq_mul_comm (m := 189) (n := n)
    simp at h_shift_9 h_shift_21 h_shift_33 h_shift_45 h_shift_57 h_shift_69 h_shift_81 h_shift_93 h_shift_105 h_shift_117 h_shift_129 h_shift_141 h_shift_153 h_shift_165 h_shift_177 h_shift_189
    have h_rot_base := cell_1618_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1619_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_9,
      ←Nat.shiftLeft_eq (b := 3),
      ←h_shift_21,
      ←h_shift_33,
      ←h_shift_45,
      ←h_shift_57,
      ←h_shift_69,
      ←h_shift_81,
      ←h_shift_93,
      ←h_shift_105,
      ←h_shift_117,
      ←h_shift_129,
      ←h_shift_141,
      ←h_shift_153,
      ←h_shift_165,
      ←h_shift_177,
      ←h_shift_189,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 21 (h := by trivial),
      bitvec_toNat_shift_add 33 (h := by trivial),
      bitvec_toNat_shift_add 45 (h := by trivial),
      bitvec_toNat_shift_add 57 (h := by trivial),
      bitvec_toNat_shift_add 69 (h := by trivial),
      bitvec_toNat_shift_add 81 (h := by trivial),
      bitvec_toNat_shift_add 93 (h := by trivial),
      bitvec_toNat_shift_add 105 (h := by trivial),
      bitvec_toNat_shift_add 117 (h := by trivial),
      bitvec_toNat_shift_add 129 (h := by trivial),
      bitvec_toNat_shift_add 141 (h := by trivial),
      bitvec_toNat_shift_add 153 (h := by trivial),
      bitvec_toNat_shift_add 165 (h := by trivial),
      bitvec_toNat_shift_add 177 (h := by trivial),
      bitvec_toNat_shift_add 189 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_1_4_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_1_4 c round = ((BitVec.ofNat 192 (os c round 1 4).val).rotateLeft (BIT_COUNT * RHO_MATRIX 1 4)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_1_4
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_689_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_690_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_691_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_692_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_693_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_694_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_695_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_744_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_745_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_746_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_747_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_748_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_749_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_750_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_751_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_6 (n) := nat_shiftLeft_eq_mul_comm (m := 6) (n := n)
    have h_shift_18 (n) := nat_shiftLeft_eq_mul_comm (m := 18) (n := n)
    have h_shift_30 (n) := nat_shiftLeft_eq_mul_comm (m := 30) (n := n)
    have h_shift_42 (n) := nat_shiftLeft_eq_mul_comm (m := 42) (n := n)
    have h_shift_54 (n) := nat_shiftLeft_eq_mul_comm (m := 54) (n := n)
    have h_shift_66 (n) := nat_shiftLeft_eq_mul_comm (m := 66) (n := n)
    have h_shift_78 (n) := nat_shiftLeft_eq_mul_comm (m := 78) (n := n)
    have h_shift_90 (n) := nat_shiftLeft_eq_mul_comm (m := 90) (n := n)
    have h_shift_102 (n) := nat_shiftLeft_eq_mul_comm (m := 102) (n := n)
    have h_shift_114 (n) := nat_shiftLeft_eq_mul_comm (m := 114) (n := n)
    have h_shift_126 (n) := nat_shiftLeft_eq_mul_comm (m := 126) (n := n)
    have h_shift_138 (n) := nat_shiftLeft_eq_mul_comm (m := 138) (n := n)
    have h_shift_150 (n) := nat_shiftLeft_eq_mul_comm (m := 150) (n := n)
    have h_shift_162 (n) := nat_shiftLeft_eq_mul_comm (m := 162) (n := n)
    have h_shift_174 (n) := nat_shiftLeft_eq_mul_comm (m := 174) (n := n)
    have h_shift_186 (n) := nat_shiftLeft_eq_mul_comm (m := 186) (n := n)
    simp at h_shift_6 h_shift_18 h_shift_30 h_shift_42 h_shift_54 h_shift_66 h_shift_78 h_shift_90 h_shift_102 h_shift_114 h_shift_126 h_shift_138 h_shift_150 h_shift_162 h_shift_174 h_shift_186
    have h_rot_base := cell_1626_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1627_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_6,
      ←Nat.shiftLeft_eq (b := 6),
      ←h_shift_18,
      ←h_shift_30,
      ←h_shift_42,
      ←h_shift_54,
      ←h_shift_66,
      ←h_shift_78,
      ←h_shift_90,
      ←h_shift_102,
      ←h_shift_114,
      ←h_shift_126,
      ←h_shift_138,
      ←h_shift_150,
      ←h_shift_162,
      ←h_shift_174,
      ←h_shift_186,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 18 (h := by trivial),
      bitvec_toNat_shift_add 30 (h := by trivial),
      bitvec_toNat_shift_add 42 (h := by trivial),
      bitvec_toNat_shift_add 54 (h := by trivial),
      bitvec_toNat_shift_add 66 (h := by trivial),
      bitvec_toNat_shift_add 78 (h := by trivial),
      bitvec_toNat_shift_add 90 (h := by trivial),
      bitvec_toNat_shift_add 102 (h := by trivial),
      bitvec_toNat_shift_add 114 (h := by trivial),
      bitvec_toNat_shift_add 126 (h := by trivial),
      bitvec_toNat_shift_add 138 (h := by trivial),
      bitvec_toNat_shift_add 150 (h := by trivial),
      bitvec_toNat_shift_add 162 (h := by trivial),
      bitvec_toNat_shift_add 174 (h := by trivial),
      bitvec_toNat_shift_add 186 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_2_0_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_2_0 c round = ((BitVec.ofNat 192 (os c round 2 0).val).rotateLeft (BIT_COUNT * RHO_MATRIX 2 0)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_2_0
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_640_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_641_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_642_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_643_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_644_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_645_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_646_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_647_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_696_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_697_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_698_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_699_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_700_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_701_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_702_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_6 (n) := nat_shiftLeft_eq_mul_comm (m := 6) (n := n)
    have h_shift_18 (n) := nat_shiftLeft_eq_mul_comm (m := 18) (n := n)
    have h_shift_30 (n) := nat_shiftLeft_eq_mul_comm (m := 30) (n := n)
    have h_shift_42 (n) := nat_shiftLeft_eq_mul_comm (m := 42) (n := n)
    have h_shift_54 (n) := nat_shiftLeft_eq_mul_comm (m := 54) (n := n)
    have h_shift_66 (n) := nat_shiftLeft_eq_mul_comm (m := 66) (n := n)
    have h_shift_78 (n) := nat_shiftLeft_eq_mul_comm (m := 78) (n := n)
    have h_shift_90 (n) := nat_shiftLeft_eq_mul_comm (m := 90) (n := n)
    have h_shift_102 (n) := nat_shiftLeft_eq_mul_comm (m := 102) (n := n)
    have h_shift_114 (n) := nat_shiftLeft_eq_mul_comm (m := 114) (n := n)
    have h_shift_126 (n) := nat_shiftLeft_eq_mul_comm (m := 126) (n := n)
    have h_shift_138 (n) := nat_shiftLeft_eq_mul_comm (m := 138) (n := n)
    have h_shift_150 (n) := nat_shiftLeft_eq_mul_comm (m := 150) (n := n)
    have h_shift_162 (n) := nat_shiftLeft_eq_mul_comm (m := 162) (n := n)
    have h_shift_174 (n) := nat_shiftLeft_eq_mul_comm (m := 174) (n := n)
    have h_shift_186 (n) := nat_shiftLeft_eq_mul_comm (m := 186) (n := n)
    simp at h_shift_6 h_shift_18 h_shift_30 h_shift_42 h_shift_54 h_shift_66 h_shift_78 h_shift_90 h_shift_102 h_shift_114 h_shift_126 h_shift_138 h_shift_150 h_shift_162 h_shift_174 h_shift_186
    have h_rot_base := cell_1598_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1599_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_6,
      ←Nat.shiftLeft_eq (b := 6),
      ←h_shift_18,
      ←h_shift_30,
      ←h_shift_42,
      ←h_shift_54,
      ←h_shift_66,
      ←h_shift_78,
      ←h_shift_90,
      ←h_shift_102,
      ←h_shift_114,
      ←h_shift_126,
      ←h_shift_138,
      ←h_shift_150,
      ←h_shift_162,
      ←h_shift_174,
      ←h_shift_186,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 18 (h := by trivial),
      bitvec_toNat_shift_add 30 (h := by trivial),
      bitvec_toNat_shift_add 42 (h := by trivial),
      bitvec_toNat_shift_add 54 (h := by trivial),
      bitvec_toNat_shift_add 66 (h := by trivial),
      bitvec_toNat_shift_add 78 (h := by trivial),
      bitvec_toNat_shift_add 90 (h := by trivial),
      bitvec_toNat_shift_add 102 (h := by trivial),
      bitvec_toNat_shift_add 114 (h := by trivial),
      bitvec_toNat_shift_add 126 (h := by trivial),
      bitvec_toNat_shift_add 138 (h := by trivial),
      bitvec_toNat_shift_add 150 (h := by trivial),
      bitvec_toNat_shift_add 162 (h := by trivial),
      bitvec_toNat_shift_add 174 (h := by trivial),
      bitvec_toNat_shift_add 186 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_2_1_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_2_1 c round = ((BitVec.ofNat 192 (os c round 2 1).val).rotateLeft (BIT_COUNT * RHO_MATRIX 2 1)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_2_1
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_476_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_478_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_479_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_528_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_529_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_530_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_531_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_532_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_533_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_534_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_535_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_536_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_537_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_538_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_539_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_6 (n) := nat_shiftLeft_eq_mul_comm (m := 6) (n := n)
    have h_shift_18 (n) := nat_shiftLeft_eq_mul_comm (m := 18) (n := n)
    have h_shift_30 (n) := nat_shiftLeft_eq_mul_comm (m := 30) (n := n)
    have h_shift_42 (n) := nat_shiftLeft_eq_mul_comm (m := 42) (n := n)
    have h_shift_54 (n) := nat_shiftLeft_eq_mul_comm (m := 54) (n := n)
    have h_shift_66 (n) := nat_shiftLeft_eq_mul_comm (m := 66) (n := n)
    have h_shift_78 (n) := nat_shiftLeft_eq_mul_comm (m := 78) (n := n)
    have h_shift_90 (n) := nat_shiftLeft_eq_mul_comm (m := 90) (n := n)
    have h_shift_102 (n) := nat_shiftLeft_eq_mul_comm (m := 102) (n := n)
    have h_shift_114 (n) := nat_shiftLeft_eq_mul_comm (m := 114) (n := n)
    have h_shift_126 (n) := nat_shiftLeft_eq_mul_comm (m := 126) (n := n)
    have h_shift_138 (n) := nat_shiftLeft_eq_mul_comm (m := 138) (n := n)
    have h_shift_150 (n) := nat_shiftLeft_eq_mul_comm (m := 150) (n := n)
    have h_shift_162 (n) := nat_shiftLeft_eq_mul_comm (m := 162) (n := n)
    have h_shift_174 (n) := nat_shiftLeft_eq_mul_comm (m := 174) (n := n)
    have h_shift_186 (n) := nat_shiftLeft_eq_mul_comm (m := 186) (n := n)
    simp at h_shift_6 h_shift_18 h_shift_30 h_shift_42 h_shift_54 h_shift_66 h_shift_78 h_shift_90 h_shift_102 h_shift_114 h_shift_126 h_shift_138 h_shift_150 h_shift_162 h_shift_174 h_shift_186
    have h_rot_base := cell_1602_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1603_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_6,
      ←Nat.shiftLeft_eq (b := 6),
      ←h_shift_18,
      ←h_shift_30,
      ←h_shift_42,
      ←h_shift_54,
      ←h_shift_66,
      ←h_shift_78,
      ←h_shift_90,
      ←h_shift_102,
      ←h_shift_114,
      ←h_shift_126,
      ←h_shift_138,
      ←h_shift_150,
      ←h_shift_162,
      ←h_shift_174,
      ←h_shift_186,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 18 (h := by trivial),
      bitvec_toNat_shift_add 30 (h := by trivial),
      bitvec_toNat_shift_add 42 (h := by trivial),
      bitvec_toNat_shift_add 54 (h := by trivial),
      bitvec_toNat_shift_add 66 (h := by trivial),
      bitvec_toNat_shift_add 78 (h := by trivial),
      bitvec_toNat_shift_add 90 (h := by trivial),
      bitvec_toNat_shift_add 102 (h := by trivial),
      bitvec_toNat_shift_add 114 (h := by trivial),
      bitvec_toNat_shift_add 126 (h := by trivial),
      bitvec_toNat_shift_add 138 (h := by trivial),
      bitvec_toNat_shift_add 150 (h := by trivial),
      bitvec_toNat_shift_add 162 (h := by trivial),
      bitvec_toNat_shift_add 174 (h := by trivial),
      bitvec_toNat_shift_add 186 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_2_2_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_2_2 c round = ((BitVec.ofNat 192 (os c round 2 2).val).rotateLeft (BIT_COUNT * RHO_MATRIX 2 2)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_2_2
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_360_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_361_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_362_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_363_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_364_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_365_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_366_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_367_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_368_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_369_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_371_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_420_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_421_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_422_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_423_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_3 (n) := nat_shiftLeft_eq_mul_comm (m := 3) (n := n)
    have h_shift_15 (n) := nat_shiftLeft_eq_mul_comm (m := 15) (n := n)
    have h_shift_27 (n) := nat_shiftLeft_eq_mul_comm (m := 27) (n := n)
    have h_shift_39 (n) := nat_shiftLeft_eq_mul_comm (m := 39) (n := n)
    have h_shift_51 (n) := nat_shiftLeft_eq_mul_comm (m := 51) (n := n)
    have h_shift_63 (n) := nat_shiftLeft_eq_mul_comm (m := 63) (n := n)
    have h_shift_75 (n) := nat_shiftLeft_eq_mul_comm (m := 75) (n := n)
    have h_shift_87 (n) := nat_shiftLeft_eq_mul_comm (m := 87) (n := n)
    have h_shift_99 (n) := nat_shiftLeft_eq_mul_comm (m := 99) (n := n)
    have h_shift_111 (n) := nat_shiftLeft_eq_mul_comm (m := 111) (n := n)
    have h_shift_123 (n) := nat_shiftLeft_eq_mul_comm (m := 123) (n := n)
    have h_shift_135 (n) := nat_shiftLeft_eq_mul_comm (m := 135) (n := n)
    have h_shift_147 (n) := nat_shiftLeft_eq_mul_comm (m := 147) (n := n)
    have h_shift_159 (n) := nat_shiftLeft_eq_mul_comm (m := 159) (n := n)
    have h_shift_171 (n) := nat_shiftLeft_eq_mul_comm (m := 171) (n := n)
    have h_shift_183 (n) := nat_shiftLeft_eq_mul_comm (m := 183) (n := n)
    simp at h_shift_3 h_shift_15 h_shift_27 h_shift_39 h_shift_51 h_shift_63 h_shift_75 h_shift_87 h_shift_99 h_shift_111 h_shift_123 h_shift_135 h_shift_147 h_shift_159 h_shift_171 h_shift_183
    have h_rot_base := cell_1611_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1610_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_3,
      ←Nat.shiftLeft_eq (b := 9),
      ←h_shift_15,
      ←h_shift_27,
      ←h_shift_39,
      ←h_shift_51,
      ←h_shift_63,
      ←h_shift_75,
      ←h_shift_87,
      ←h_shift_99,
      ←h_shift_111,
      ←h_shift_123,
      ←h_shift_135,
      ←h_shift_147,
      ←h_shift_159,
      ←h_shift_171,
      ←h_shift_183,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 15 (h := by trivial),
      bitvec_toNat_shift_add 27 (h := by trivial),
      bitvec_toNat_shift_add 39 (h := by trivial),
      bitvec_toNat_shift_add 51 (h := by trivial),
      bitvec_toNat_shift_add 63 (h := by trivial),
      bitvec_toNat_shift_add 75 (h := by trivial),
      bitvec_toNat_shift_add 87 (h := by trivial),
      bitvec_toNat_shift_add 99 (h := by trivial),
      bitvec_toNat_shift_add 111 (h := by trivial),
      bitvec_toNat_shift_add 123 (h := by trivial),
      bitvec_toNat_shift_add 135 (h := by trivial),
      bitvec_toNat_shift_add 147 (h := by trivial),
      bitvec_toNat_shift_add 159 (h := by trivial),
      bitvec_toNat_shift_add 171 (h := by trivial),
      bitvec_toNat_shift_add 183 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_2_3_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_2_3 c round = ((BitVec.ofNat 192 (os c round 2 3).val).rotateLeft (BIT_COUNT * RHO_MATRIX 2 3)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_2_3
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_612_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_613_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_614_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_616_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_617_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_618_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_619_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_620_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_621_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_622_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_623_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_672_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_673_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_674_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_675_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_3 (n) := nat_shiftLeft_eq_mul_comm (m := 3) (n := n)
    have h_shift_15 (n) := nat_shiftLeft_eq_mul_comm (m := 15) (n := n)
    have h_shift_27 (n) := nat_shiftLeft_eq_mul_comm (m := 27) (n := n)
    have h_shift_39 (n) := nat_shiftLeft_eq_mul_comm (m := 39) (n := n)
    have h_shift_51 (n) := nat_shiftLeft_eq_mul_comm (m := 51) (n := n)
    have h_shift_63 (n) := nat_shiftLeft_eq_mul_comm (m := 63) (n := n)
    have h_shift_75 (n) := nat_shiftLeft_eq_mul_comm (m := 75) (n := n)
    have h_shift_87 (n) := nat_shiftLeft_eq_mul_comm (m := 87) (n := n)
    have h_shift_99 (n) := nat_shiftLeft_eq_mul_comm (m := 99) (n := n)
    have h_shift_111 (n) := nat_shiftLeft_eq_mul_comm (m := 111) (n := n)
    have h_shift_123 (n) := nat_shiftLeft_eq_mul_comm (m := 123) (n := n)
    have h_shift_135 (n) := nat_shiftLeft_eq_mul_comm (m := 135) (n := n)
    have h_shift_147 (n) := nat_shiftLeft_eq_mul_comm (m := 147) (n := n)
    have h_shift_159 (n) := nat_shiftLeft_eq_mul_comm (m := 159) (n := n)
    have h_shift_171 (n) := nat_shiftLeft_eq_mul_comm (m := 171) (n := n)
    have h_shift_183 (n) := nat_shiftLeft_eq_mul_comm (m := 183) (n := n)
    simp at h_shift_3 h_shift_15 h_shift_27 h_shift_39 h_shift_51 h_shift_63 h_shift_75 h_shift_87 h_shift_99 h_shift_111 h_shift_123 h_shift_135 h_shift_147 h_shift_159 h_shift_171 h_shift_183
    have h_rot_base := cell_1621_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1620_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_3,
      ←Nat.shiftLeft_eq (b := 9),
      ←h_shift_15,
      ←h_shift_27,
      ←h_shift_39,
      ←h_shift_51,
      ←h_shift_63,
      ←h_shift_75,
      ←h_shift_87,
      ←h_shift_99,
      ←h_shift_111,
      ←h_shift_123,
      ←h_shift_135,
      ←h_shift_147,
      ←h_shift_159,
      ←h_shift_171,
      ←h_shift_183,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 15 (h := by trivial),
      bitvec_toNat_shift_add 27 (h := by trivial),
      bitvec_toNat_shift_add 39 (h := by trivial),
      bitvec_toNat_shift_add 51 (h := by trivial),
      bitvec_toNat_shift_add 63 (h := by trivial),
      bitvec_toNat_shift_add 75 (h := by trivial),
      bitvec_toNat_shift_add 87 (h := by trivial),
      bitvec_toNat_shift_add 99 (h := by trivial),
      bitvec_toNat_shift_add 111 (h := by trivial),
      bitvec_toNat_shift_add 123 (h := by trivial),
      bitvec_toNat_shift_add 135 (h := by trivial),
      bitvec_toNat_shift_add 147 (h := by trivial),
      bitvec_toNat_shift_add 159 (h := by trivial),
      bitvec_toNat_shift_add 171 (h := by trivial),
      bitvec_toNat_shift_add 183 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_2_4_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_2_4 c round = ((BitVec.ofNat 192 (os c round 2 4).val).rotateLeft (BIT_COUNT * RHO_MATRIX 2 4)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_2_4
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_448_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_449_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_450_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_451_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_452_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_453_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_454_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_455_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_504_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_505_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_506_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_507_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_508_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_509_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_510_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_9 (n) := nat_shiftLeft_eq_mul_comm (m := 9) (n := n)
    have h_shift_21 (n) := nat_shiftLeft_eq_mul_comm (m := 21) (n := n)
    have h_shift_33 (n) := nat_shiftLeft_eq_mul_comm (m := 33) (n := n)
    have h_shift_45 (n) := nat_shiftLeft_eq_mul_comm (m := 45) (n := n)
    have h_shift_57 (n) := nat_shiftLeft_eq_mul_comm (m := 57) (n := n)
    have h_shift_69 (n) := nat_shiftLeft_eq_mul_comm (m := 69) (n := n)
    have h_shift_81 (n) := nat_shiftLeft_eq_mul_comm (m := 81) (n := n)
    have h_shift_93 (n) := nat_shiftLeft_eq_mul_comm (m := 93) (n := n)
    have h_shift_105 (n) := nat_shiftLeft_eq_mul_comm (m := 105) (n := n)
    have h_shift_117 (n) := nat_shiftLeft_eq_mul_comm (m := 117) (n := n)
    have h_shift_129 (n) := nat_shiftLeft_eq_mul_comm (m := 129) (n := n)
    have h_shift_141 (n) := nat_shiftLeft_eq_mul_comm (m := 141) (n := n)
    have h_shift_153 (n) := nat_shiftLeft_eq_mul_comm (m := 153) (n := n)
    have h_shift_165 (n) := nat_shiftLeft_eq_mul_comm (m := 165) (n := n)
    have h_shift_177 (n) := nat_shiftLeft_eq_mul_comm (m := 177) (n := n)
    have h_shift_189 (n) := nat_shiftLeft_eq_mul_comm (m := 189) (n := n)
    simp at h_shift_9 h_shift_21 h_shift_33 h_shift_45 h_shift_57 h_shift_69 h_shift_81 h_shift_93 h_shift_105 h_shift_117 h_shift_129 h_shift_141 h_shift_153 h_shift_165 h_shift_177 h_shift_189
    have h_rot_base := cell_1628_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1629_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_9,
      ←Nat.shiftLeft_eq (b := 3),
      ←h_shift_21,
      ←h_shift_33,
      ←h_shift_45,
      ←h_shift_57,
      ←h_shift_69,
      ←h_shift_81,
      ←h_shift_93,
      ←h_shift_105,
      ←h_shift_117,
      ←h_shift_129,
      ←h_shift_141,
      ←h_shift_153,
      ←h_shift_165,
      ←h_shift_177,
      ←h_shift_189,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 21 (h := by trivial),
      bitvec_toNat_shift_add 33 (h := by trivial),
      bitvec_toNat_shift_add 45 (h := by trivial),
      bitvec_toNat_shift_add 57 (h := by trivial),
      bitvec_toNat_shift_add 69 (h := by trivial),
      bitvec_toNat_shift_add 81 (h := by trivial),
      bitvec_toNat_shift_add 93 (h := by trivial),
      bitvec_toNat_shift_add 105 (h := by trivial),
      bitvec_toNat_shift_add 117 (h := by trivial),
      bitvec_toNat_shift_add 129 (h := by trivial),
      bitvec_toNat_shift_add 141 (h := by trivial),
      bitvec_toNat_shift_add 153 (h := by trivial),
      bitvec_toNat_shift_add 165 (h := by trivial),
      bitvec_toNat_shift_add 177 (h := by trivial),
      bitvec_toNat_shift_add 189 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_3_0_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_3_0 c round = ((BitVec.ofNat 192 (os c round 3 0).val).rotateLeft (BIT_COUNT * RHO_MATRIX 3 0)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def
    ] at h_s_rot_parts
    unfold rho_s_3_0
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 4096 < P by omega), add_assoc, -BitVec.toNat_rotateLeft
    ]
    have h_cell_0 := (cell_400_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_401_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_402_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_403_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_404_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_405_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_406_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_407_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_456_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_457_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_458_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_459_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_460_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_461_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_462_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_463_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_12 (n) := nat_shiftLeft_eq_mul_comm (m := 12) (n := n)
    have h_shift_24 (n) := nat_shiftLeft_eq_mul_comm (m := 24) (n := n)
    have h_shift_36 (n) := nat_shiftLeft_eq_mul_comm (m := 36) (n := n)
    have h_shift_48 (n) := nat_shiftLeft_eq_mul_comm (m := 48) (n := n)
    have h_shift_60 (n) := nat_shiftLeft_eq_mul_comm (m := 60) (n := n)
    have h_shift_72 (n) := nat_shiftLeft_eq_mul_comm (m := 72) (n := n)
    have h_shift_84 (n) := nat_shiftLeft_eq_mul_comm (m := 84) (n := n)
    have h_shift_96 (n) := nat_shiftLeft_eq_mul_comm (m := 96) (n := n)
    have h_shift_108 (n) := nat_shiftLeft_eq_mul_comm (m := 108) (n := n)
    have h_shift_120 (n) := nat_shiftLeft_eq_mul_comm (m := 120) (n := n)
    have h_shift_132 (n) := nat_shiftLeft_eq_mul_comm (m := 132) (n := n)
    have h_shift_144 (n) := nat_shiftLeft_eq_mul_comm (m := 144) (n := n)
    have h_shift_156 (n) := nat_shiftLeft_eq_mul_comm (m := 156) (n := n)
    have h_shift_168 (n) := nat_shiftLeft_eq_mul_comm (m := 168) (n := n)
    have h_shift_180 (n) := nat_shiftLeft_eq_mul_comm (m := 180) (n := n)
    simp at h_shift_12 h_shift_24 h_shift_36 h_shift_48 h_shift_60 h_shift_72 h_shift_84 h_shift_96 h_shift_108 h_shift_120 h_shift_132 h_shift_144 h_shift_156 h_shift_168 h_shift_180
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      h_bitvec h_cell_15,
      ←h_shift_12,
      ←h_shift_24,
      ←h_shift_36,
      ←h_shift_48,
      ←h_shift_60,
      ←h_shift_72,
      ←h_shift_84,
      ←h_shift_96,
      ←h_shift_108,
      ←h_shift_120,
      ←h_shift_132,
      ←h_shift_144,
      ←h_shift_156,
      ←h_shift_168,
      ←h_shift_180,
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_3_1_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_3_1 c round = ((BitVec.ofNat 192 (os c round 3 1).val).rotateLeft (BIT_COUNT * RHO_MATRIX 3 1)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_3_1
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_652_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_653_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_654_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_655_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_656_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_657_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_658_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_659_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_708_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_709_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_710_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_711_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_712_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_714_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_715_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_3 (n) := nat_shiftLeft_eq_mul_comm (m := 3) (n := n)
    have h_shift_15 (n) := nat_shiftLeft_eq_mul_comm (m := 15) (n := n)
    have h_shift_27 (n) := nat_shiftLeft_eq_mul_comm (m := 27) (n := n)
    have h_shift_39 (n) := nat_shiftLeft_eq_mul_comm (m := 39) (n := n)
    have h_shift_51 (n) := nat_shiftLeft_eq_mul_comm (m := 51) (n := n)
    have h_shift_63 (n) := nat_shiftLeft_eq_mul_comm (m := 63) (n := n)
    have h_shift_75 (n) := nat_shiftLeft_eq_mul_comm (m := 75) (n := n)
    have h_shift_87 (n) := nat_shiftLeft_eq_mul_comm (m := 87) (n := n)
    have h_shift_99 (n) := nat_shiftLeft_eq_mul_comm (m := 99) (n := n)
    have h_shift_111 (n) := nat_shiftLeft_eq_mul_comm (m := 111) (n := n)
    have h_shift_123 (n) := nat_shiftLeft_eq_mul_comm (m := 123) (n := n)
    have h_shift_135 (n) := nat_shiftLeft_eq_mul_comm (m := 135) (n := n)
    have h_shift_147 (n) := nat_shiftLeft_eq_mul_comm (m := 147) (n := n)
    have h_shift_159 (n) := nat_shiftLeft_eq_mul_comm (m := 159) (n := n)
    have h_shift_171 (n) := nat_shiftLeft_eq_mul_comm (m := 171) (n := n)
    have h_shift_183 (n) := nat_shiftLeft_eq_mul_comm (m := 183) (n := n)
    simp at h_shift_3 h_shift_15 h_shift_27 h_shift_39 h_shift_51 h_shift_63 h_shift_75 h_shift_87 h_shift_99 h_shift_111 h_shift_123 h_shift_135 h_shift_147 h_shift_159 h_shift_171 h_shift_183
    have h_rot_base := cell_1605_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1604_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_3,
      ←Nat.shiftLeft_eq (b := 9),
      ←h_shift_15,
      ←h_shift_27,
      ←h_shift_39,
      ←h_shift_51,
      ←h_shift_63,
      ←h_shift_75,
      ←h_shift_87,
      ←h_shift_99,
      ←h_shift_111,
      ←h_shift_123,
      ←h_shift_135,
      ←h_shift_147,
      ←h_shift_159,
      ←h_shift_171,
      ←h_shift_183,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 15 (h := by trivial),
      bitvec_toNat_shift_add 27 (h := by trivial),
      bitvec_toNat_shift_add 39 (h := by trivial),
      bitvec_toNat_shift_add 51 (h := by trivial),
      bitvec_toNat_shift_add 63 (h := by trivial),
      bitvec_toNat_shift_add 75 (h := by trivial),
      bitvec_toNat_shift_add 87 (h := by trivial),
      bitvec_toNat_shift_add 99 (h := by trivial),
      bitvec_toNat_shift_add 111 (h := by trivial),
      bitvec_toNat_shift_add 123 (h := by trivial),
      bitvec_toNat_shift_add 135 (h := by trivial),
      bitvec_toNat_shift_add 147 (h := by trivial),
      bitvec_toNat_shift_add 159 (h := by trivial),
      bitvec_toNat_shift_add 171 (h := by trivial),
      bitvec_toNat_shift_add 183 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_3_2_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_3_2 c round = ((BitVec.ofNat 192 (os c round 3 2).val).rotateLeft (BIT_COUNT * RHO_MATRIX 3 2)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_3_2
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_488_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_489_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_490_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_491_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_540_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_541_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_543_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_544_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_545_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_546_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_547_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_548_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_549_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_550_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_551_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_9 (n) := nat_shiftLeft_eq_mul_comm (m := 9) (n := n)
    have h_shift_21 (n) := nat_shiftLeft_eq_mul_comm (m := 21) (n := n)
    have h_shift_33 (n) := nat_shiftLeft_eq_mul_comm (m := 33) (n := n)
    have h_shift_45 (n) := nat_shiftLeft_eq_mul_comm (m := 45) (n := n)
    have h_shift_57 (n) := nat_shiftLeft_eq_mul_comm (m := 57) (n := n)
    have h_shift_69 (n) := nat_shiftLeft_eq_mul_comm (m := 69) (n := n)
    have h_shift_81 (n) := nat_shiftLeft_eq_mul_comm (m := 81) (n := n)
    have h_shift_93 (n) := nat_shiftLeft_eq_mul_comm (m := 93) (n := n)
    have h_shift_105 (n) := nat_shiftLeft_eq_mul_comm (m := 105) (n := n)
    have h_shift_117 (n) := nat_shiftLeft_eq_mul_comm (m := 117) (n := n)
    have h_shift_129 (n) := nat_shiftLeft_eq_mul_comm (m := 129) (n := n)
    have h_shift_141 (n) := nat_shiftLeft_eq_mul_comm (m := 141) (n := n)
    have h_shift_153 (n) := nat_shiftLeft_eq_mul_comm (m := 153) (n := n)
    have h_shift_165 (n) := nat_shiftLeft_eq_mul_comm (m := 165) (n := n)
    have h_shift_177 (n) := nat_shiftLeft_eq_mul_comm (m := 177) (n := n)
    have h_shift_189 (n) := nat_shiftLeft_eq_mul_comm (m := 189) (n := n)
    simp at h_shift_9 h_shift_21 h_shift_33 h_shift_45 h_shift_57 h_shift_69 h_shift_81 h_shift_93 h_shift_105 h_shift_117 h_shift_129 h_shift_141 h_shift_153 h_shift_165 h_shift_177 h_shift_189
    have h_rot_base := cell_1612_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1613_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_9,
      ←Nat.shiftLeft_eq (b := 3),
      ←h_shift_21,
      ←h_shift_33,
      ←h_shift_45,
      ←h_shift_57,
      ←h_shift_69,
      ←h_shift_81,
      ←h_shift_93,
      ←h_shift_105,
      ←h_shift_117,
      ←h_shift_129,
      ←h_shift_141,
      ←h_shift_153,
      ←h_shift_165,
      ←h_shift_177,
      ←h_shift_189,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 21 (h := by trivial),
      bitvec_toNat_shift_add 33 (h := by trivial),
      bitvec_toNat_shift_add 45 (h := by trivial),
      bitvec_toNat_shift_add 57 (h := by trivial),
      bitvec_toNat_shift_add 69 (h := by trivial),
      bitvec_toNat_shift_add 81 (h := by trivial),
      bitvec_toNat_shift_add 93 (h := by trivial),
      bitvec_toNat_shift_add 105 (h := by trivial),
      bitvec_toNat_shift_add 117 (h := by trivial),
      bitvec_toNat_shift_add 129 (h := by trivial),
      bitvec_toNat_shift_add 141 (h := by trivial),
      bitvec_toNat_shift_add 153 (h := by trivial),
      bitvec_toNat_shift_add 165 (h := by trivial),
      bitvec_toNat_shift_add 177 (h := by trivial),
      bitvec_toNat_shift_add 189 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_3_3_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_3_3 c round = ((BitVec.ofNat 192 (os c round 3 3).val).rotateLeft (BIT_COUNT * RHO_MATRIX 3 3)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_3_3
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_372_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_373_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_374_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_375_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_376_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_378_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_379_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_380_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_381_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_382_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_383_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_432_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_433_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_434_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_435_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_9 (n) := nat_shiftLeft_eq_mul_comm (m := 9) (n := n)
    have h_shift_21 (n) := nat_shiftLeft_eq_mul_comm (m := 21) (n := n)
    have h_shift_33 (n) := nat_shiftLeft_eq_mul_comm (m := 33) (n := n)
    have h_shift_45 (n) := nat_shiftLeft_eq_mul_comm (m := 45) (n := n)
    have h_shift_57 (n) := nat_shiftLeft_eq_mul_comm (m := 57) (n := n)
    have h_shift_69 (n) := nat_shiftLeft_eq_mul_comm (m := 69) (n := n)
    have h_shift_81 (n) := nat_shiftLeft_eq_mul_comm (m := 81) (n := n)
    have h_shift_93 (n) := nat_shiftLeft_eq_mul_comm (m := 93) (n := n)
    have h_shift_105 (n) := nat_shiftLeft_eq_mul_comm (m := 105) (n := n)
    have h_shift_117 (n) := nat_shiftLeft_eq_mul_comm (m := 117) (n := n)
    have h_shift_129 (n) := nat_shiftLeft_eq_mul_comm (m := 129) (n := n)
    have h_shift_141 (n) := nat_shiftLeft_eq_mul_comm (m := 141) (n := n)
    have h_shift_153 (n) := nat_shiftLeft_eq_mul_comm (m := 153) (n := n)
    have h_shift_165 (n) := nat_shiftLeft_eq_mul_comm (m := 165) (n := n)
    have h_shift_177 (n) := nat_shiftLeft_eq_mul_comm (m := 177) (n := n)
    have h_shift_189 (n) := nat_shiftLeft_eq_mul_comm (m := 189) (n := n)
    simp at h_shift_9 h_shift_21 h_shift_33 h_shift_45 h_shift_57 h_shift_69 h_shift_81 h_shift_93 h_shift_105 h_shift_117 h_shift_129 h_shift_141 h_shift_153 h_shift_165 h_shift_177 h_shift_189
    have h_rot_base := cell_1622_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1623_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_9,
      ←Nat.shiftLeft_eq (b := 3),
      ←h_shift_21,
      ←h_shift_33,
      ←h_shift_45,
      ←h_shift_57,
      ←h_shift_69,
      ←h_shift_81,
      ←h_shift_93,
      ←h_shift_105,
      ←h_shift_117,
      ←h_shift_129,
      ←h_shift_141,
      ←h_shift_153,
      ←h_shift_165,
      ←h_shift_177,
      ←h_shift_189,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 21 (h := by trivial),
      bitvec_toNat_shift_add 33 (h := by trivial),
      bitvec_toNat_shift_add 45 (h := by trivial),
      bitvec_toNat_shift_add 57 (h := by trivial),
      bitvec_toNat_shift_add 69 (h := by trivial),
      bitvec_toNat_shift_add 81 (h := by trivial),
      bitvec_toNat_shift_add 93 (h := by trivial),
      bitvec_toNat_shift_add 105 (h := by trivial),
      bitvec_toNat_shift_add 117 (h := by trivial),
      bitvec_toNat_shift_add 129 (h := by trivial),
      bitvec_toNat_shift_add 141 (h := by trivial),
      bitvec_toNat_shift_add 153 (h := by trivial),
      bitvec_toNat_shift_add 165 (h := by trivial),
      bitvec_toNat_shift_add 177 (h := by trivial),
      bitvec_toNat_shift_add 189 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_3_4_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_3_4 c round = ((BitVec.ofNat 192 (os c round 3 4).val).rotateLeft (BIT_COUNT * RHO_MATRIX 3 4)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    unfold rho_s_3_4
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 4096 < P by omega), add_assoc, -BitVec.toNat_rotateLeft
    ]
    have h_cell_0 := (cell_624_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_625_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_626_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_627_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_628_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_629_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_630_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_631_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_632_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_633_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_634_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_635_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_684_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_685_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_686_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_687_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_12 (n) := nat_shiftLeft_eq_mul_comm (m := 12) (n := n)
    have h_shift_24 (n) := nat_shiftLeft_eq_mul_comm (m := 24) (n := n)
    have h_shift_36 (n) := nat_shiftLeft_eq_mul_comm (m := 36) (n := n)
    have h_shift_48 (n) := nat_shiftLeft_eq_mul_comm (m := 48) (n := n)
    have h_shift_60 (n) := nat_shiftLeft_eq_mul_comm (m := 60) (n := n)
    have h_shift_72 (n) := nat_shiftLeft_eq_mul_comm (m := 72) (n := n)
    have h_shift_84 (n) := nat_shiftLeft_eq_mul_comm (m := 84) (n := n)
    have h_shift_96 (n) := nat_shiftLeft_eq_mul_comm (m := 96) (n := n)
    have h_shift_108 (n) := nat_shiftLeft_eq_mul_comm (m := 108) (n := n)
    have h_shift_120 (n) := nat_shiftLeft_eq_mul_comm (m := 120) (n := n)
    have h_shift_132 (n) := nat_shiftLeft_eq_mul_comm (m := 132) (n := n)
    have h_shift_144 (n) := nat_shiftLeft_eq_mul_comm (m := 144) (n := n)
    have h_shift_156 (n) := nat_shiftLeft_eq_mul_comm (m := 156) (n := n)
    have h_shift_168 (n) := nat_shiftLeft_eq_mul_comm (m := 168) (n := n)
    have h_shift_180 (n) := nat_shiftLeft_eq_mul_comm (m := 180) (n := n)
    simp at h_shift_12 h_shift_24 h_shift_36 h_shift_48 h_shift_60 h_shift_72 h_shift_84 h_shift_96 h_shift_108 h_shift_120 h_shift_132 h_shift_144 h_shift_156 h_shift_168 h_shift_180
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      h_bitvec h_cell_15,
      ←h_shift_12,
      ←h_shift_24,
      ←h_shift_36,
      ←h_shift_48,
      ←h_shift_60,
      ←h_shift_72,
      ←h_shift_84,
      ←h_shift_96,
      ←h_shift_108,
      ←h_shift_120,
      ←h_shift_132,
      ←h_shift_144,
      ←h_shift_156,
      ←h_shift_168,
      ←h_shift_180,
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_4_0_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_4_0 c round = ((BitVec.ofNat 192 (os c round 4 0).val).rotateLeft (BIT_COUNT * RHO_MATRIX 4 0)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_4_0
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_576_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_577_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_578_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_579_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_580_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_581_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_583_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_584_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_585_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_586_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_587_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_636_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_637_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_638_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_639_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_3 (n) := nat_shiftLeft_eq_mul_comm (m := 3) (n := n)
    have h_shift_15 (n) := nat_shiftLeft_eq_mul_comm (m := 15) (n := n)
    have h_shift_27 (n) := nat_shiftLeft_eq_mul_comm (m := 27) (n := n)
    have h_shift_39 (n) := nat_shiftLeft_eq_mul_comm (m := 39) (n := n)
    have h_shift_51 (n) := nat_shiftLeft_eq_mul_comm (m := 51) (n := n)
    have h_shift_63 (n) := nat_shiftLeft_eq_mul_comm (m := 63) (n := n)
    have h_shift_75 (n) := nat_shiftLeft_eq_mul_comm (m := 75) (n := n)
    have h_shift_87 (n) := nat_shiftLeft_eq_mul_comm (m := 87) (n := n)
    have h_shift_99 (n) := nat_shiftLeft_eq_mul_comm (m := 99) (n := n)
    have h_shift_111 (n) := nat_shiftLeft_eq_mul_comm (m := 111) (n := n)
    have h_shift_123 (n) := nat_shiftLeft_eq_mul_comm (m := 123) (n := n)
    have h_shift_135 (n) := nat_shiftLeft_eq_mul_comm (m := 135) (n := n)
    have h_shift_147 (n) := nat_shiftLeft_eq_mul_comm (m := 147) (n := n)
    have h_shift_159 (n) := nat_shiftLeft_eq_mul_comm (m := 159) (n := n)
    have h_shift_171 (n) := nat_shiftLeft_eq_mul_comm (m := 171) (n := n)
    have h_shift_183 (n) := nat_shiftLeft_eq_mul_comm (m := 183) (n := n)
    simp at h_shift_3 h_shift_15 h_shift_27 h_shift_39 h_shift_51 h_shift_63 h_shift_75 h_shift_87 h_shift_99 h_shift_111 h_shift_123 h_shift_135 h_shift_147 h_shift_159 h_shift_171 h_shift_183
    have h_rot_base := cell_1601_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1600_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_3,
      ←Nat.shiftLeft_eq (b := 9),
      ←h_shift_15,
      ←h_shift_27,
      ←h_shift_39,
      ←h_shift_51,
      ←h_shift_63,
      ←h_shift_75,
      ←h_shift_87,
      ←h_shift_99,
      ←h_shift_111,
      ←h_shift_123,
      ←h_shift_135,
      ←h_shift_147,
      ←h_shift_159,
      ←h_shift_171,
      ←h_shift_183,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 15 (h := by trivial),
      bitvec_toNat_shift_add 27 (h := by trivial),
      bitvec_toNat_shift_add 39 (h := by trivial),
      bitvec_toNat_shift_add 51 (h := by trivial),
      bitvec_toNat_shift_add 63 (h := by trivial),
      bitvec_toNat_shift_add 75 (h := by trivial),
      bitvec_toNat_shift_add 87 (h := by trivial),
      bitvec_toNat_shift_add 99 (h := by trivial),
      bitvec_toNat_shift_add 111 (h := by trivial),
      bitvec_toNat_shift_add 123 (h := by trivial),
      bitvec_toNat_shift_add 135 (h := by trivial),
      bitvec_toNat_shift_add 147 (h := by trivial),
      bitvec_toNat_shift_add 159 (h := by trivial),
      bitvec_toNat_shift_add 171 (h := by trivial),
      bitvec_toNat_shift_add 183 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_4_1_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_4_1 c round = ((BitVec.ofNat 192 (os c round 4 1).val).rotateLeft (BIT_COUNT * RHO_MATRIX 4 1)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    unfold rho_s_4_1
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 4096 < P by omega), add_assoc, -BitVec.toNat_rotateLeft
    ]
    have h_cell_0 := (cell_412_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_413_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_414_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_415_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_416_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_417_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_418_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_419_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_468_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_469_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_470_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_471_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_472_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_473_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_474_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_475_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_12 (n) := nat_shiftLeft_eq_mul_comm (m := 12) (n := n)
    have h_shift_24 (n) := nat_shiftLeft_eq_mul_comm (m := 24) (n := n)
    have h_shift_36 (n) := nat_shiftLeft_eq_mul_comm (m := 36) (n := n)
    have h_shift_48 (n) := nat_shiftLeft_eq_mul_comm (m := 48) (n := n)
    have h_shift_60 (n) := nat_shiftLeft_eq_mul_comm (m := 60) (n := n)
    have h_shift_72 (n) := nat_shiftLeft_eq_mul_comm (m := 72) (n := n)
    have h_shift_84 (n) := nat_shiftLeft_eq_mul_comm (m := 84) (n := n)
    have h_shift_96 (n) := nat_shiftLeft_eq_mul_comm (m := 96) (n := n)
    have h_shift_108 (n) := nat_shiftLeft_eq_mul_comm (m := 108) (n := n)
    have h_shift_120 (n) := nat_shiftLeft_eq_mul_comm (m := 120) (n := n)
    have h_shift_132 (n) := nat_shiftLeft_eq_mul_comm (m := 132) (n := n)
    have h_shift_144 (n) := nat_shiftLeft_eq_mul_comm (m := 144) (n := n)
    have h_shift_156 (n) := nat_shiftLeft_eq_mul_comm (m := 156) (n := n)
    have h_shift_168 (n) := nat_shiftLeft_eq_mul_comm (m := 168) (n := n)
    have h_shift_180 (n) := nat_shiftLeft_eq_mul_comm (m := 180) (n := n)
    simp at h_shift_12 h_shift_24 h_shift_36 h_shift_48 h_shift_60 h_shift_72 h_shift_84 h_shift_96 h_shift_108 h_shift_120 h_shift_132 h_shift_144 h_shift_156 h_shift_168 h_shift_180
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      h_bitvec h_cell_15,
      ←h_shift_12,
      ←h_shift_24,
      ←h_shift_36,
      ←h_shift_48,
      ←h_shift_60,
      ←h_shift_72,
      ←h_shift_84,
      ←h_shift_96,
      ←h_shift_108,
      ←h_shift_120,
      ←h_shift_132,
      ←h_shift_144,
      ←h_shift_156,
      ←h_shift_168,
      ←h_shift_180,
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_4_2_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_4_2 c round = ((BitVec.ofNat 192 (os c round 4 2).val).rotateLeft (BIT_COUNT * RHO_MATRIX 4 2)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_4_2
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_664_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_665_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_666_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_667_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_668_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_669_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_670_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_671_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_720_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_722_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_723_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_724_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_725_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_726_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_727_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_3 (n) := nat_shiftLeft_eq_mul_comm (m := 3) (n := n)
    have h_shift_15 (n) := nat_shiftLeft_eq_mul_comm (m := 15) (n := n)
    have h_shift_27 (n) := nat_shiftLeft_eq_mul_comm (m := 27) (n := n)
    have h_shift_39 (n) := nat_shiftLeft_eq_mul_comm (m := 39) (n := n)
    have h_shift_51 (n) := nat_shiftLeft_eq_mul_comm (m := 51) (n := n)
    have h_shift_63 (n) := nat_shiftLeft_eq_mul_comm (m := 63) (n := n)
    have h_shift_75 (n) := nat_shiftLeft_eq_mul_comm (m := 75) (n := n)
    have h_shift_87 (n) := nat_shiftLeft_eq_mul_comm (m := 87) (n := n)
    have h_shift_99 (n) := nat_shiftLeft_eq_mul_comm (m := 99) (n := n)
    have h_shift_111 (n) := nat_shiftLeft_eq_mul_comm (m := 111) (n := n)
    have h_shift_123 (n) := nat_shiftLeft_eq_mul_comm (m := 123) (n := n)
    have h_shift_135 (n) := nat_shiftLeft_eq_mul_comm (m := 135) (n := n)
    have h_shift_147 (n) := nat_shiftLeft_eq_mul_comm (m := 147) (n := n)
    have h_shift_159 (n) := nat_shiftLeft_eq_mul_comm (m := 159) (n := n)
    have h_shift_171 (n) := nat_shiftLeft_eq_mul_comm (m := 171) (n := n)
    have h_shift_183 (n) := nat_shiftLeft_eq_mul_comm (m := 183) (n := n)
    simp at h_shift_3 h_shift_15 h_shift_27 h_shift_39 h_shift_51 h_shift_63 h_shift_75 h_shift_87 h_shift_99 h_shift_111 h_shift_123 h_shift_135 h_shift_147 h_shift_159 h_shift_171 h_shift_183
    have h_rot_base := cell_1615_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1614_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_3,
      ←Nat.shiftLeft_eq (b := 9),
      ←h_shift_15,
      ←h_shift_27,
      ←h_shift_39,
      ←h_shift_51,
      ←h_shift_63,
      ←h_shift_75,
      ←h_shift_87,
      ←h_shift_99,
      ←h_shift_111,
      ←h_shift_123,
      ←h_shift_135,
      ←h_shift_147,
      ←h_shift_159,
      ←h_shift_171,
      ←h_shift_183,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 15 (h := by trivial),
      bitvec_toNat_shift_add 27 (h := by trivial),
      bitvec_toNat_shift_add 39 (h := by trivial),
      bitvec_toNat_shift_add 51 (h := by trivial),
      bitvec_toNat_shift_add 63 (h := by trivial),
      bitvec_toNat_shift_add 75 (h := by trivial),
      bitvec_toNat_shift_add 87 (h := by trivial),
      bitvec_toNat_shift_add 99 (h := by trivial),
      bitvec_toNat_shift_add 111 (h := by trivial),
      bitvec_toNat_shift_add 123 (h := by trivial),
      bitvec_toNat_shift_add 135 (h := by trivial),
      bitvec_toNat_shift_add 147 (h := by trivial),
      bitvec_toNat_shift_add 159 (h := by trivial),
      bitvec_toNat_shift_add 171 (h := by trivial),
      bitvec_toNat_shift_add 183 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_4_3_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 3*Normalize.mask < P):
    rho_s_4_3 c round = ((BitVec.ofNat 192 (os c round 4 3).val).rotateLeft (BIT_COUNT * RHO_MATRIX 4 3)).toNat
  := by
    simp [Normalize.mask.eq_def] at h_P
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    unfold rho_s_4_3
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 4096 < P by omega), add_assoc, -BitVec.toNat_rotateLeft
    ]
    have h_cell_0 := (cell_500_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_501_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_502_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_503_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_552_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_553_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_554_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_555_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_556_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_557_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_558_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_559_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_560_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_561_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_562_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_563_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_12 (n) := nat_shiftLeft_eq_mul_comm (m := 12) (n := n)
    have h_shift_24 (n) := nat_shiftLeft_eq_mul_comm (m := 24) (n := n)
    have h_shift_36 (n) := nat_shiftLeft_eq_mul_comm (m := 36) (n := n)
    have h_shift_48 (n) := nat_shiftLeft_eq_mul_comm (m := 48) (n := n)
    have h_shift_60 (n) := nat_shiftLeft_eq_mul_comm (m := 60) (n := n)
    have h_shift_72 (n) := nat_shiftLeft_eq_mul_comm (m := 72) (n := n)
    have h_shift_84 (n) := nat_shiftLeft_eq_mul_comm (m := 84) (n := n)
    have h_shift_96 (n) := nat_shiftLeft_eq_mul_comm (m := 96) (n := n)
    have h_shift_108 (n) := nat_shiftLeft_eq_mul_comm (m := 108) (n := n)
    have h_shift_120 (n) := nat_shiftLeft_eq_mul_comm (m := 120) (n := n)
    have h_shift_132 (n) := nat_shiftLeft_eq_mul_comm (m := 132) (n := n)
    have h_shift_144 (n) := nat_shiftLeft_eq_mul_comm (m := 144) (n := n)
    have h_shift_156 (n) := nat_shiftLeft_eq_mul_comm (m := 156) (n := n)
    have h_shift_168 (n) := nat_shiftLeft_eq_mul_comm (m := 168) (n := n)
    have h_shift_180 (n) := nat_shiftLeft_eq_mul_comm (m := 180) (n := n)
    simp at h_shift_12 h_shift_24 h_shift_36 h_shift_48 h_shift_60 h_shift_72 h_shift_84 h_shift_96 h_shift_108 h_shift_120 h_shift_132 h_shift_144 h_shift_156 h_shift_168 h_shift_180
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      h_bitvec h_cell_15,
      ←h_shift_12,
      ←h_shift_24,
      ←h_shift_36,
      ←h_shift_48,
      ←h_shift_60,
      ←h_shift_72,
      ←h_shift_84,
      ←h_shift_96,
      ←h_shift_108,
      ←h_shift_120,
      ←h_shift_132,
      ←h_shift_144,
      ←h_shift_156,
      ←h_shift_168,
      ←h_shift_180,
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide

  lemma rho_s_4_4_rotation {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    rho_s_4_4 c round = ((BitVec.ofNat 192 (os c round 4 4).val).rotateLeft (BIT_COUNT * RHO_MATRIX 4 4)).toNat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, fin_vals
    ] at h_s_input_parts
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, rho_pi_chi_cells.eq_def,
      fin_vals
    ] at h_s_rot_parts
    rewrite [add_comm] at h_s_rot_parts
    unfold rho_s_4_4
    rewrite [←h_s_rot_parts]
    rewrite [←h_s_input_parts]
    simp [
      Decode.expr.eq_def, keccak_constants, mul_add,
      ←mul_assoc, ←pow_add, ZMod.val_add, ZMod.val_mul,
      fin_vals, List.rotateLeft, zmod_pow_simps,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      add_assoc, -BitVec.toNat_rotateLeft,
      s_parts_cell_offsets, pi_region_start
    ]
    have h_cell_0 := (cell_384_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_385_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_386_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_388_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_389_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_390_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_391_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_392_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_393_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_394_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_395_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_444_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_445_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_446_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_447_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_bitvec {a: ℕ} (h: a ≤ 1755): a = (BitVec.ofNat 12 a).toNat := by simp; omega
    have h_shift_6 (n) := nat_shiftLeft_eq_mul_comm (m := 6) (n := n)
    have h_shift_18 (n) := nat_shiftLeft_eq_mul_comm (m := 18) (n := n)
    have h_shift_30 (n) := nat_shiftLeft_eq_mul_comm (m := 30) (n := n)
    have h_shift_42 (n) := nat_shiftLeft_eq_mul_comm (m := 42) (n := n)
    have h_shift_54 (n) := nat_shiftLeft_eq_mul_comm (m := 54) (n := n)
    have h_shift_66 (n) := nat_shiftLeft_eq_mul_comm (m := 66) (n := n)
    have h_shift_78 (n) := nat_shiftLeft_eq_mul_comm (m := 78) (n := n)
    have h_shift_90 (n) := nat_shiftLeft_eq_mul_comm (m := 90) (n := n)
    have h_shift_102 (n) := nat_shiftLeft_eq_mul_comm (m := 102) (n := n)
    have h_shift_114 (n) := nat_shiftLeft_eq_mul_comm (m := 114) (n := n)
    have h_shift_126 (n) := nat_shiftLeft_eq_mul_comm (m := 126) (n := n)
    have h_shift_138 (n) := nat_shiftLeft_eq_mul_comm (m := 138) (n := n)
    have h_shift_150 (n) := nat_shiftLeft_eq_mul_comm (m := 150) (n := n)
    have h_shift_162 (n) := nat_shiftLeft_eq_mul_comm (m := 162) (n := n)
    have h_shift_174 (n) := nat_shiftLeft_eq_mul_comm (m := 174) (n := n)
    have h_shift_186 (n) := nat_shiftLeft_eq_mul_comm (m := 186) (n := n)
    simp at h_shift_6 h_shift_18 h_shift_30 h_shift_42 h_shift_54 h_shift_66 h_shift_78 h_shift_90 h_shift_102 h_shift_114 h_shift_126 h_shift_138 h_shift_150 h_shift_162 h_shift_174 h_shift_186
    have h_rot_base := cell_1630_rot_part_base h_meets_constraints h_round (by omega)
    have h_rot_mul := cell_1631_rot_part_mul h_meets_constraints h_round (by omega)
    have h_rot_bitvec {k n: ℕ} (h: n < 2^k): n = (BitVec.ofNat k n).toNat := by simp; rw [Nat.mod_eq_of_lt h]
    rewrite [
      Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega),
      h_rot_bitvec h_rot_mul,
      h_rot_bitvec h_rot_base,
      h_bitvec h_cell_0,
      h_bitvec h_cell_1,
      h_bitvec h_cell_2,
      h_bitvec h_cell_3,
      h_bitvec h_cell_4,
      h_bitvec h_cell_5,
      h_bitvec h_cell_6,
      h_bitvec h_cell_7,
      h_bitvec h_cell_8,
      h_bitvec h_cell_9,
      h_bitvec h_cell_10,
      h_bitvec h_cell_11,
      h_bitvec h_cell_12,
      h_bitvec h_cell_13,
      h_bitvec h_cell_14,
      ←h_shift_6,
      ←Nat.shiftLeft_eq (b := 6),
      ←h_shift_18,
      ←h_shift_30,
      ←h_shift_42,
      ←h_shift_54,
      ←h_shift_66,
      ←h_shift_78,
      ←h_shift_90,
      ←h_shift_102,
      ←h_shift_114,
      ←h_shift_126,
      ←h_shift_138,
      ←h_shift_150,
      ←h_shift_162,
      ←h_shift_174,
      ←h_shift_186,
      bitvec_toNat_shift_add 12 (h := by trivial),
      bitvec_toNat_shift_add 24 (h := by trivial),
      bitvec_toNat_shift_add 36 (h := by trivial),
      bitvec_toNat_shift_add 48 (h := by trivial),
      bitvec_toNat_shift_add 60 (h := by trivial),
      bitvec_toNat_shift_add 72 (h := by trivial),
      bitvec_toNat_shift_add 84 (h := by trivial),
      bitvec_toNat_shift_add 96 (h := by trivial),
      bitvec_toNat_shift_add 108 (h := by trivial),
      bitvec_toNat_shift_add 120 (h := by trivial),
      bitvec_toNat_shift_add 132 (h := by trivial),
      bitvec_toNat_shift_add 144 (h := by trivial),
      bitvec_toNat_shift_add 156 (h := by trivial),
      bitvec_toNat_shift_add 168 (h := by trivial),
      bitvec_toNat_shift_add 180 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      bitvec_toNat_shift_add 18 (h := by trivial),
      bitvec_toNat_shift_add 30 (h := by trivial),
      bitvec_toNat_shift_add 42 (h := by trivial),
      bitvec_toNat_shift_add 54 (h := by trivial),
      bitvec_toNat_shift_add 66 (h := by trivial),
      bitvec_toNat_shift_add 78 (h := by trivial),
      bitvec_toNat_shift_add 90 (h := by trivial),
      bitvec_toNat_shift_add 102 (h := by trivial),
      bitvec_toNat_shift_add 114 (h := by trivial),
      bitvec_toNat_shift_add 126 (h := by trivial),
      bitvec_toNat_shift_add 138 (h := by trivial),
      bitvec_toNat_shift_add 150 (h := by trivial),
      bitvec_toNat_shift_add 162 (h := by trivial),
      bitvec_toNat_shift_add 174 (h := by trivial),
      bitvec_toNat_shift_add 186 (h := by trivial),
      bitvec_toNat_shift_add 192 (h := by trivial),
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
    ]
    bv_decide
end Keccak.Soundness

import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.Lookups.Normalize_3.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Iota
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Attributes
import Examples.Scroll.Keccak.Soundness.Constants
import Examples.Scroll.Keccak.Soundness.IotaParts
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness

  lemma iota_state_size (h_state: state.size ≥ 25):
    (LeanCrypto.HashFunctions.ι roundNumber state).size ≥ 25
  := by
    simp_all [LeanCrypto.HashFunctions.ι.eq_def]

  lemma roundConstants_indexing (h_round: round ∈ Finset.Icc 1 24):
    round - 1 < LeanCrypto.HashFunctions.RoundConstants.size
  := by
    simp_all [LeanCrypto.HashFunctions.RoundConstants.eq_def]
    omega

  lemma iota_s_roundConstant {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: 114781288875642162538711578024368757323014499555913773950098 < P) (h_round: round ∈ Finset.Icc 1 24) :
    iota_s c round x y = match x, y with
      | 0, 0 => Normalize.normalize_unpacked (
          os' c round x y +
          (UInt64_to_unpacked_Nat (LeanCrypto.HashFunctions.RoundConstants[round-1]'(roundConstants_indexing h_round)): ZMod P)
        ).val 64
      | x, y => os' c round x y
  := by
    have ne_zero: NeZero P := by
      constructor
      simp_all [Nat.Prime.ne_zero]
    by_cases x = 0 <;> by_cases y = 0
    . simp_all [
        iota_s.eq_def, iota_s_0_0_transform.eq_def,
        Transform.split_expr.eq_def, Split.expr_res.eq_def,
        keccak_constants, word_parts_known,
        Decode.expr.eq_def, mul_add, ←mul_assoc, ←pow_add
      ]
      simp [normalize_iota, *, show P ≥ 74899 by simp_all [Normalize.mask.eq_def]; omega]
      simp only [zmod_pow_shift_simps, add_assoc, ←Nat.cast_add]
      congr
      rewrite [
        iota_parts_0_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_1_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_2_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_3_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_4_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_5_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_6_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_7_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_8_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_9_to_bitvec h_meets_constraints h_round (by omega),
        iota_parts_10_to_bitvec' h_meets_constraints h_round (by omega)
      ]
      rewrite [
        mul_comm (2^18), ←Nat.shiftLeft_eq,
        mul_comm (2^36), ←Nat.shiftLeft_eq,
        mul_comm (2^54), ←Nat.shiftLeft_eq,
        mul_comm (2^72), ←Nat.shiftLeft_eq,
        mul_comm (2^90), ←Nat.shiftLeft_eq,
        mul_comm (2^108), ←Nat.shiftLeft_eq,
        mul_comm (2^126), ←Nat.shiftLeft_eq,
        mul_comm (2^144), ←Nat.shiftLeft_eq,
        mul_comm (2^162), ←Nat.shiftLeft_eq,
        mul_comm (2^180), ←Nat.shiftLeft_eq
      ]
      simp only [ZMod.val_natCast, keccak_constants]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [Nat.mod_eq_of_lt (by {simp_all [Normalize.mask.eq_def]; omega})]
      rewrite [bitvec_ofNat_toNat_eq (4*3) 12 (n := (cell_manager c round 1642).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1641).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1640).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1639).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1638).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1637).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1636).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1635).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1634).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1633).val) (by trivial)]
      rewrite [bitvec_ofNat_toNat_eq (6*3) 18 (n := (cell_manager c round 1632).val) (by trivial)]
      rewrite [Normalize.normalize_6_shift_18_add, bitvec_18_toNat_shift_add 36 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_36_add, bitvec_18_toNat_shift_add 54 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_54_add, bitvec_18_toNat_shift_add 72 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_72_add, bitvec_18_toNat_shift_add 90 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_90_add, bitvec_18_toNat_shift_add 108 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_108_add, bitvec_18_toNat_shift_add 126 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_126_add, bitvec_18_toNat_shift_add 144 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_144_add, bitvec_18_toNat_shift_add 162 (h := by trivial)]
      rewrite [Normalize.normalize_6_shift_162_add, bitvec_18_toNat_shift_add 180 (h := by trivial)]
      rewrite [Normalize.normalize_shrink_6_4, Normalize.normalize_6_shift_180_add]
      congr 1
      simp
      have h_cell_1642 := (cell_1642_small_range h_meets_constraints h_round h_P)
      have h_cell_1641 := (cell_1641_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1640 := (cell_1640_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1639 := (cell_1639_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1638 := (cell_1638_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1637 := (cell_1637_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1636 := (cell_1636_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1635 := (cell_1635_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1634 := (cell_1634_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1633 := (cell_1633_normalize_3_input_range h_meets_constraints h_round (by omega))
      have h_cell_1632 := (cell_1632_normalize_3_input_range h_meets_constraints h_round (by omega))
      rewrite [
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1642 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1641 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1641 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1640 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1640 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1639 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1639 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1638 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1638 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1637 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1637 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1636 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1636 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1635 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1635 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1634 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1634 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1633 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1633 (by trivial)),
        Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1632 (by trivial)),
        Nat.mod_eq_of_lt (a := _ <<< 18 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 54 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 90 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 126 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
        Nat.mod_eq_of_lt (a := _ <<< 162 + _) (by omega)
      ]
      -- have h_iota := iota_parts.eq_def (P_Prime := P_Prime) c round
      have h_iota := Proofs.iota_parts_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
      simp [
        iota_parts.eq_def,
        Split.expr.eq_def,
        Split.expr_res.eq_def,
        Split.constraint.eq_def,
        list_ops,
        keccak_constants,
        word_parts_known,
        Decode.expr.eq_def, mul_add, ←mul_assoc,
        ←pow_add
      ] at h_iota
      simp only [Nat.shiftLeft_eq]
      have one_lt_p: Fact (1 < P) := by constructor; omega
      have h_2pow18: ((2: ZMod P)^18).val = 2^18 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow36: ((2: ZMod P)^36).val = 2^36 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow54: ((2: ZMod P)^54).val = 2^54 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow72: ((2: ZMod P)^72).val = 2^72 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow90: ((2: ZMod P)^90).val = 2^90 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow108: ((2: ZMod P)^108).val = 2^108 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow126: ((2: ZMod P)^126).val = 2^126 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow144: ((2: ZMod P)^144).val = 2^144 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow162: ((2: ZMod P)^162).val = 2^162 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      have h_2pow180: ((2: ZMod P)^180).val = 2^180 := by
        rw [ZMod.val_pow, ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        rewrite [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [
        show (cell_manager c round 1642).val * 2^180 = (2^180 * (cell_manager c round 1642)).val by {
          rw [ZMod.val_mul, h_2pow180, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1641).val * 2^162 = (2^162 * (cell_manager c round 1641)).val by {
          rw [ZMod.val_mul, h_2pow162, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1640).val * 2^144 = (2^144 * (cell_manager c round 1640)).val by {
          rw [ZMod.val_mul, h_2pow144, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1639).val * 2^126 = (2^126 * (cell_manager c round 1639)).val by {
          rw [ZMod.val_mul, h_2pow126, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1638).val * 2^108 = (2^108 * (cell_manager c round 1638)).val by {
          rw [ZMod.val_mul, h_2pow108, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1637).val * 2^90 = (2^90 * (cell_manager c round 1637)).val by {
          rw [ZMod.val_mul, h_2pow90, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1636).val * 2^72= (2^72 * (cell_manager c round 1636)).val by {
          rw [ZMod.val_mul, h_2pow72, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1635).val * 2^54 = (2^54 * (cell_manager c round 1635)).val by {
          rw [ZMod.val_mul, h_2pow54, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1634).val * 2^36 = (2^36 * (cell_manager c round 1634)).val by {
          rw [ZMod.val_mul, h_2pow36, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
        show (cell_manager c round 1633).val * 2^18 = (2^18 * (cell_manager c round 1633)).val by {
          rw [ZMod.val_mul, h_2pow18, mul_comm, Nat.mod_eq_of_lt]
          omega
        },
      ]
      have :
        (2 ^ 180 * cell_manager c round 1642).val +
          ((2 ^ 162 * cell_manager c round 1641).val +
            ((2 ^ 144 * cell_manager c round 1640).val +
              ((2 ^ 126 * cell_manager c round 1639).val +
                ((2 ^ 108 * cell_manager c round 1638).val +
                  ((2 ^ 90 * cell_manager c round 1637).val +
                    ((2 ^ 72 * cell_manager c round 1636).val +
                      ((2 ^ 54 * cell_manager c round 1635).val +
                        ((2 ^ 36 * cell_manager c round 1634).val +
                          ((2 ^ 18 * cell_manager c round 1633).val +
                            (cell_manager c round 1632).val))))))))) =
        (2 ^ 180 * cell_manager c round 1642 + 2 ^ 162 * cell_manager c round 1641 + 2 ^ 144 * cell_manager c round 1640 +
                      2 ^ 126 * cell_manager c round 1639 +
                    2 ^ 108 * cell_manager c round 1638 +
                  2 ^ 90 * cell_manager c round 1637 +
                2 ^ 72 * cell_manager c round 1636 +
              2 ^ 54 * cell_manager c round 1635 +
            2 ^ 36 * cell_manager c round 1634 +
          2 ^ 18 * cell_manager c round 1633 +
        cell_manager c round 1632).val
      := by
        simp [
          ZMod.val_add, ZMod.val_mul,
          h_2pow18, h_2pow36,
          h_2pow54, h_2pow72,
          h_2pow90, h_2pow108,
          h_2pow126, h_2pow144,
          h_2pow162, h_2pow180
        ]
        rewrite [
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega),
        ]
        simp only [add_assoc]
      rewrite [h_iota] at this
      unfold iota_input at this
      have h_row: get_num_rows_per_round * round < 312 := by
        simp [keccak_constants]
        have h_round := Finset.mem_Icc.mp h_round
        omega
      have h_round_cst := round_cst_eq_unpacked_RoundConstants h_meets_constraints (by omega) h_row
      rewrite [Nat.mul_div_cancel_left] at h_round_cst
      . convert this using 3
        rewrite [List.getElem?_eq_getElem] at h_round_cst
        . simp at h_round_cst
          rewrite [List.getElem_cons, dite_cond_eq_false, List.getElem_append, dite_cond_eq_true, Array.getElem_toList] at h_round_cst
          . rewrite [←h_round_cst]
            simp
          . have := (Finset.mem_Icc.mp h_round).2
            simp [LeanCrypto.HashFunctions.RoundConstants.eq_def]
            omega
          . have := (Finset.mem_Icc.mp h_round).1
            simp
            omega
          . have := (Finset.mem_Icc.mp h_round).2
            simp [LeanCrypto.HashFunctions.RoundConstants.eq_def]
            omega
      . simp [keccak_constants]
    all_goals (
      simp_all [
        LeanCrypto.HashFunctions.ι.eq_def,
        state_get.eq_def,
        iota_s.eq_def
      ]
    )

end Keccak.Soundness

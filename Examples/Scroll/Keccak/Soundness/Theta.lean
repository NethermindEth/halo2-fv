import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Theta
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Bc
import Examples.Scroll.Keccak.Soundness.BcRange
import Examples.Scroll.Keccak.Soundness.Lookups
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.SRange
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness

  lemma θ_indexed_eval (h_size: state.size ≥ 25):
    (Array.range 25).zip (LeanCrypto.HashFunctions.θ.d state) = #[
      (0, state[20] ^^^ state[21] ^^^ state[22] ^^^ state[23] ^^^ state[24] ^^^ LeanCrypto.rotateL (state[5]  ^^^ state[6]  ^^^ state[7]  ^^^ state[8]  ^^^ state[9] ) 1),
      (1, state[0]  ^^^ state[1]  ^^^ state[2]  ^^^ state[3]  ^^^ state[4]  ^^^ LeanCrypto.rotateL (state[10] ^^^ state[11] ^^^ state[12] ^^^ state[13] ^^^ state[14]) 1),
      (2, state[5]  ^^^ state[6]  ^^^ state[7]  ^^^ state[8]  ^^^ state[9]  ^^^ LeanCrypto.rotateL (state[15] ^^^ state[16] ^^^ state[17] ^^^ state[18] ^^^ state[19]) 1),
      (3, state[10] ^^^ state[11] ^^^ state[12] ^^^ state[13] ^^^ state[14] ^^^ LeanCrypto.rotateL (state[20] ^^^ state[21] ^^^ state[22] ^^^ state[23] ^^^ state[24]) 1),
      (4, state[15] ^^^ state[16] ^^^ state[17] ^^^ state[18] ^^^ state[19] ^^^ LeanCrypto.rotateL (state[0]  ^^^ state[1]  ^^^ state[2]  ^^^ state[3]  ^^^ state[4] ) 1)]
  := by
    unfold LeanCrypto.HashFunctions.θ.d LeanCrypto.HashFunctions.θ.c
    simp [array_range_5, array_range_25]
    rewrite [
      array_extract_5 (x := 0) (by omega),
      array_extract_5 (x := 5) (by omega),
      array_extract_5 (x := 10) (by omega),
      array_extract_5 (x := 15) (by omega),
      array_extract_5 (x := 20) (by omega)
    ]
    simp [array_foldl_xor_5]

  lemma take_get_0 {l: List T} (h_length: l.length = 5) (h_j: j < 5): (l ++ l1)[j]'(by simp_all; omega) = l[j] := by
    simp_all [List.getElem_append]

  lemma take_get_5 {l: List T} (h_length: l.length = 5) (h_length1: l1.length = 5) (h_j: j < 5): (l ++ (l1 ++ l2))[5+j]? = l1[j]? := by
    simp_all [List.getElem?_append]

  -- lemma take_get_10 (h_length: l.length ≥ 5) (h_length1: l1.length ≥ 5) (h_length2: l2.length ≥ 5) (h_j: j < 5): (List.take 5 l ++ (List.take 5 l1 ++ (List.take 5 l2 ++ l3)))[10+j]? = l2[j]? := by
  --   simp_all [List.getElem?_append]

  -- lemma take_get_15 (h_length: l.length ≥ 5) (h_length1: l1.length ≥ 5) (h_length2: l2.length ≥ 5) (h_length3: l3.length ≥ 5) (h_j: j < 5): (List.take 5 l ++ (List.take 5 l1 ++ (List.take 5 l2 ++ (List.take 5 l3 ++ l4))))[15+j]? = l3[j]? := by
  --   simp_all [List.getElem?_append]

  -- lemma take_get_20 (h_length: l.length ≥ 5) (h_length1: l1.length ≥ 5) (h_length2: l2.length ≥ 5) (h_length3: l3.length ≥ 5) (h_j: j < 5): (List.take 5 l ++ (List.take 5 l1 ++ (List.take 5 l2 ++ (List.take 5 l3 ++ l4))))[20+j]? = l4[j]? := by
  --   simp_all [List.getElem?_append]
  --   rewrite [if_neg, if_neg, if_neg, if_neg]
  --   congr 1
  --   all_goals omega

  lemma theta_d_size: (LeanCrypto.HashFunctions.θ.d state).size = 5 := by
    unfold LeanCrypto.HashFunctions.θ.d
    simp

  lemma theta_state_size (h_state_size: state.size ≥ 25): (LeanCrypto.HashFunctions.θ state).size ≥ 25 := by
    simp [
      LeanCrypto.HashFunctions.θ.eq_def, θ_indexed_eval,
      LeanCrypto.HashFunctions.θ.d.eq_def,
      LeanCrypto.HashFunctions.θ.c.eq_def,
      array_range_5
    ]
    rewrite [
      array_extract_5 (x := 0) (by omega),
      array_extract_5 (x := 5) (by omega),
      array_extract_5 (x := 10) (by omega),
      array_extract_5 (x := 15) (by omega),
      array_extract_5 (x := 20) (by omega),
      ←Array.sum_eq_sum_toList
    ]
    simp [list_ops]
    repeat rewrite [min_eq_left (by omega)]
    simp

  lemma decode_bc  {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P) (idx: Fin 5):
    (Decode.expr (bc c round idx).1).val = Normalize.normalize_unpacked (
      s c round idx 0 +
      s c round idx 1 +
      s c round idx 2 +
      s c round idx 3 +
      s c round idx 4
    ).val 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_P_nom : 366 ≤ P := by omega
    simp [
      bc.eq_def, keccak_constants, Transform.split_expr.eq_def,
      Split.expr_res.eq_def, word_parts_known, normalize_bc, *
    ]
    rewrite [bc_top_part_normalized_range idx h_meets_constraints h_round h_P]
    simp [Decode.expr.eq_def, keccak_constants, ZMod.val_add, ZMod.val_mul]
    have h_2_pow_9 :((2: ZMod P)^9).val = 2^9 := by
      convert ZMod.val_pow _
      . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
      . constructor; omega
      . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]; omega
    rewrite [h_2_pow_9]
    simp only [mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd]
    simp only [←nat_shiftLeft_eq_mul_comm]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat
        (show 3 = BIT_COUNT*1 by simp [keccak_constants])
        (x := (cell_manager _ _ _).val),
      ←Normalize.normalize_unpacked_ofNat_toNat
        (show 9 = BIT_COUNT*3 by simp [keccak_constants])
        (x := (cell_manager _ _ _).val),
      add_assoc
    ]
    rewrite [
      Normalize.normalize_3_shift_9_add, bitvec_toNat_shift_add 18 (h := by trivial),
      Normalize.normalize_3_shift_18_add, bitvec_toNat_shift_add 27 (h := by trivial),
      Normalize.normalize_3_shift_27_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_3_shift_36_add, bitvec_toNat_shift_add 45 (h := by trivial),
      Normalize.normalize_3_shift_45_add, bitvec_toNat_shift_add 54 (h := by trivial),
      Normalize.normalize_3_shift_54_add, bitvec_toNat_shift_add 63 (h := by trivial),
      Normalize.normalize_3_shift_63_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_3_shift_72_add, bitvec_toNat_shift_add 81 (h := by trivial),
      Normalize.normalize_3_shift_81_add, bitvec_toNat_shift_add 90 (h := by trivial),
      Normalize.normalize_3_shift_90_add, bitvec_toNat_shift_add 99 (h := by trivial),
      Normalize.normalize_3_shift_99_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_3_shift_108_add, bitvec_toNat_shift_add 117 (h := by trivial),
      Normalize.normalize_3_shift_117_add, bitvec_toNat_shift_add 126 (h := by trivial),
      Normalize.normalize_3_shift_126_add, bitvec_toNat_shift_add 135 (h := by trivial),
      Normalize.normalize_3_shift_135_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_3_shift_144_add, bitvec_toNat_shift_add 153 (h := by trivial),
      Normalize.normalize_3_shift_153_add, bitvec_toNat_shift_add 162 (h := by trivial),
      Normalize.normalize_3_shift_162_add, bitvec_toNat_shift_add 171 (h := by trivial),
      Normalize.normalize_3_shift_171_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_3_shift_180_add, bitvec_toNat_shift_add 189 (h := by trivial),
      Normalize.normalize_1_shift_189_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    have (a b c: ℕ) (h: b ≤ c) (h_b: b > 0): a % b % c = a % b := by
      rw [Nat.mod_eq_of_lt]
      exact lt_of_lt_of_le (Nat.mod_lt _ h_b) h
    simp [this]; clear this
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask (by unfold Normalize.mask; omega)),
      Nat.mod_eq_of_lt (a := _ <<< 9 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 18 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 27 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 45 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 54 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 63 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 81 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 90 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 99 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 117 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 126 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 135 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 153 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 162 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 171 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 189 + _) (by omega),
    ]
    have h_c_parts := Proofs.c_parts_of_meets_constraints h_meets_constraints round h_round idx
    simp [
      c_parts.eq_def, Split.expr.eq_def, keccak_constants,
      Split.constraint.eq_def, Split.expr_res, word_parts_known
    ] at h_c_parts
    have h_s_sum:
      ((
        (s c round idx 0).val +
        ((s c round idx 1).val +
        ((s c round idx 2).val +
        ((s c round idx 3).val +
        (s c round idx 4).val)))
      ) % P) =
      (s c round idx 0 + s c round idx 1 + s c round idx 2 + s c round idx 3 + s c round idx 4).val
    := by
      simp [ZMod.val_add, add_assoc]
    rewrite [h_s_sum, ←h_c_parts]; clear h_s_sum h_c_parts
    simp [Decode.expr.eq_def, keccak_constants, ZMod.val_add, ZMod.val_mul]
    simp only [h_2_pow_9, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd]
    simp only [←nat_shiftLeft_eq_mul_comm, ←add_assoc]
    have h_P_bc : 8 < P := by omega
    have := bc_0_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_1_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_2_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_3_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_4_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_5_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_6_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_7_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_8_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_9_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_10_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_11_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_12_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_13_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_14_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_15_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_16_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_17_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_18_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_19_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_20_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
    have := bc_top_part_range idx h_meets_constraints h_round h_P
    simp (disch := omega) [Nat.mod_eq_of_lt]

  lemma decode_bc_rotated {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P) (idx: Fin 5):
      (Decode.expr ((bc c round idx).1.rotateRight 1)).val =
      ((BitVec.ofNat 192
        (Normalize.normalize_unpacked (
          (s c round idx 0).val +
          (s c round idx 1).val +
          (s c round idx 2).val +
          (s c round idx 3).val +
          (s c round idx 4).val
        ) 64)
      ).rotateLeft BIT_COUNT).toNat
    := by
      have : NeZero P := by constructor; exact P_Prime.ne_zero
      have h_P_nom : 366 ≤ P := by omega
      have h_c_parts := Proofs.c_parts_of_meets_constraints h_meets_constraints round h_round idx
      simp [
        c_parts.eq_def, Split.expr.eq_def, keccak_constants,
        Split.constraint.eq_def, Split.expr_res, word_parts_known,
        -Fin.val_one, -Fin.val_one'
      ] at h_c_parts
      have h_s_0:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 0)
      have h_s_1:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 1)
      have h_s_2:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 2)
      have h_s_3:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 3)
      have h_s_4:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 4)
      have h_s_sum:
        (s c round idx 0).val +
        (s c round idx 1).val +
        (s c round idx 2).val +
        (s c round idx 3).val +
        (s c round idx 4).val =
        (s c round idx 0 + s c round idx 1 + s c round idx 2 + s c round idx 3 + s c round idx 4).val
      := by
        simp_all [ZMod.val_add, Normalize.mask.eq_def]
        rw [Nat.mod_eq_of_lt (by omega)]
      rewrite [h_s_sum, ←h_c_parts]; clear h_s_sum h_c_parts h_s_0 h_s_1 h_s_2 h_s_3 h_s_4
      simp [
        bc.eq_def, keccak_constants, Transform.split_expr.eq_def,
        Split.expr_res.eq_def, word_parts_known, normalize_bc, *,
        List.rotateRight,
        -Fin.val_one, -Fin.val_one', -BitVec.toNat_rotateLeft
      ]
      rewrite [bc_top_part_normalized_range idx h_meets_constraints h_round h_P]
      simp [
        Decode.expr.eq_def, keccak_constants, ZMod.val_add, ZMod.val_mul,
        -Fin.val_one, -Fin.val_one', -BitVec.toNat_rotateLeft
      ]
      have h_2_pow_3 :((2: ZMod P)^3).val = 2^3 := by
        convert ZMod.val_pow _
        . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        . constructor; omega
        . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]; omega
      have h_2_pow_9 :((2: ZMod P)^9).val = 2^9 := by
        convert ZMod.val_pow _
        . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
        . constructor; omega
        . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]; omega
      rewrite [h_2_pow_3, h_2_pow_9]
      simp only [mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd]
      simp only [←nat_shiftLeft_eq_mul_comm]

      have h_P_bc : 8 < P := by omega
      have h_cell_1 := bc_0_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_2 := bc_1_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_3 := bc_2_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_4 := bc_3_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_5 := bc_4_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_6 := bc_5_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_7 := bc_6_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_8 := bc_7_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_9 := bc_8_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_10 := bc_9_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_11 := bc_10_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_12 := bc_11_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_13 := bc_12_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_14 := bc_13_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_15 := bc_14_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_16 := bc_15_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_17 := bc_16_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_18 := bc_17_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_19 := bc_18_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_20 := bc_19_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_21 := bc_20_normalize_6_input_range h_meets_constraints h_round h_P_bc idx
      have h_cell_22 := bc_top_part_range idx h_meets_constraints h_round h_P

      have h_to_bitvec (x: ℕ) (h: x ≤ 365): x = (BitVec.ofNat 9 x).toNat := by
        simp (disch := omega) [Nat.mod_eq_of_lt]
      have h_to_bitvec_small (x: ℕ) (h: x ≤ 5): x = (BitVec.ofNat 3 x).toNat := by
        simp (disch := omega) [Nat.mod_eq_of_lt]

      rewrite [
        Nat.mod_eq_of_lt (by {
          simp [
            Normalize.normalize_unpacked.eq_def,
            keccak_constants, Normalize.mask,
            Nat.and_assoc, -Nat.and_one_is_mod,
          ]
          simp only [Nat.shiftLeft_eq]
          replace h_cell_1 := Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 21)).val) (m := 1)
          replace h_cell_2 := Nat.mul_le_mul_right (2^3) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx)).val) (m := 73))
          replace h_cell_3 := Nat.mul_le_mul_right (2^12) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 1)).val) (m := 73))
          replace h_cell_4 := Nat.mul_le_mul_right (2^21) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 2)).val) (m := 73))
          replace h_cell_5 := Nat.mul_le_mul_right (2^30) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 3)).val) (m := 73))
          replace h_cell_6 := Nat.mul_le_mul_right (2^39) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 4)).val) (m := 73))
          replace h_cell_7 := Nat.mul_le_mul_right (2^48) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 5)).val) (m := 73))
          replace h_cell_8 := Nat.mul_le_mul_right (2^57) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 6)).val) (m := 73))
          replace h_cell_9 := Nat.mul_le_mul_right (2^66) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 7)).val) (m := 73))
          replace h_cell_10 := Nat.mul_le_mul_right (2^75) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 8)).val) (m := 73))
          replace h_cell_11 := Nat.mul_le_mul_right (2^84) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 9)).val) (m := 73))
          replace h_cell_12 := Nat.mul_le_mul_right (2^93) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 10)).val) (m := 73))
          replace h_cell_13 := Nat.mul_le_mul_right (2^102) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 11)).val) (m := 73))
          replace h_cell_14 := Nat.mul_le_mul_right (2^111) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 12)).val) (m := 73))
          replace h_cell_15 := Nat.mul_le_mul_right (2^120) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 13)).val) (m := 73))
          replace h_cell_16 := Nat.mul_le_mul_right (2^129) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 14)).val) (m := 73))
          replace h_cell_17 := Nat.mul_le_mul_right (2^138) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 15)).val) (m := 73))
          replace h_cell_18 := Nat.mul_le_mul_right (2^147) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 16)).val) (m := 73))
          replace h_cell_19 := Nat.mul_le_mul_right (2^156) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 17)).val) (m := 73))
          replace h_cell_20 := Nat.mul_le_mul_right (2^165) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 18)).val) (m := 73))
          replace h_cell_21 := Nat.mul_le_mul_right (2^174) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 19)).val) (m := 73))
          replace h_cell_22 := Nat.mul_le_mul_right (2^183) (Nat.and_le_right (n := (cell_manager c round (96 + 22 * ↑idx + 20)).val) (m := 73))
          apply lt_of_le_of_lt
            (add_le_add
              (add_le_add
                (add_le_add
                  (add_le_add
                    (add_le_add
                      (add_le_add
                        (add_le_add
                          (add_le_add
                            (add_le_add
                              (add_le_add
                                (add_le_add
                                  (add_le_add
                                    (add_le_add
                                      (add_le_add
                                        (add_le_add
                                          (add_le_add
                                            (add_le_add
                                              (add_le_add
                                                (add_le_add
                                                  (add_le_add
                                                    (add_le_add h_cell_22 h_cell_21)
                                                    h_cell_20)
                                                  h_cell_19)
                                                h_cell_18)
                                              h_cell_17)
                                            h_cell_16)
                                          h_cell_15)
                                        h_cell_14)
                                      h_cell_13)
                                    h_cell_12)
                                  h_cell_11)
                                h_cell_10)
                              h_cell_9)
                            h_cell_8)
                          h_cell_7)
                        h_cell_6)
                      h_cell_5)
                    h_cell_4)
                  h_cell_3)
                h_cell_2)
              h_cell_1)
          norm_num
          omega
        }),
        Nat.mod_eq_of_lt (by omega)
      ]

      rewrite [
        h_to_bitvec _ h_cell_1,
        h_to_bitvec _ h_cell_2,
        h_to_bitvec _ h_cell_3,
        h_to_bitvec _ h_cell_4,
        h_to_bitvec _ h_cell_5,
        h_to_bitvec _ h_cell_6,
        h_to_bitvec _ h_cell_7,
        h_to_bitvec _ h_cell_8,
        h_to_bitvec _ h_cell_9,
        h_to_bitvec _ h_cell_10,
        h_to_bitvec _ h_cell_11,
        h_to_bitvec _ h_cell_12,
        h_to_bitvec _ h_cell_13,
        h_to_bitvec _ h_cell_14,
        h_to_bitvec _ h_cell_15,
        h_to_bitvec _ h_cell_16,
        h_to_bitvec _ h_cell_17,
        h_to_bitvec _ h_cell_18,
        h_to_bitvec _ h_cell_19,
        h_to_bitvec _ h_cell_20,
        h_to_bitvec _ h_cell_21,
        h_to_bitvec_small _ h_cell_22
      ]

      simp only [
        ←Normalize.normalize_unpacked_ofNat_toNat
          (show 3 = BIT_COUNT*1 by simp [keccak_constants])
          (x := (cell_manager _ _ _).val),
        ←Normalize.normalize_unpacked_ofNat_toNat
          (show 9 = BIT_COUNT*3 by simp [keccak_constants])
          (x := (cell_manager _ _ _).val),
        add_assoc
      ]
      rewrite [
        Normalize.normalize_3_shift_3_add, bitvec_toNat_shift_add 12 (h := by trivial),
        Normalize.normalize_3_shift_12_add, bitvec_toNat_shift_add 21 (h := by trivial),
        Normalize.normalize_3_shift_21_add, bitvec_toNat_shift_add 30 (h := by trivial),
        Normalize.normalize_3_shift_30_add, bitvec_toNat_shift_add 39 (h := by trivial),
        Normalize.normalize_3_shift_39_add, bitvec_toNat_shift_add 48 (h := by trivial),
        Normalize.normalize_3_shift_48_add, bitvec_toNat_shift_add 57 (h := by trivial),
        Normalize.normalize_3_shift_57_add, bitvec_toNat_shift_add 66 (h := by trivial),
        Normalize.normalize_3_shift_66_add, bitvec_toNat_shift_add 75 (h := by trivial),
        Normalize.normalize_3_shift_75_add, bitvec_toNat_shift_add 84 (h := by trivial),
        Normalize.normalize_3_shift_84_add, bitvec_toNat_shift_add 93 (h := by trivial),
        Normalize.normalize_3_shift_93_add, bitvec_toNat_shift_add 102 (h := by trivial),
        Normalize.normalize_3_shift_102_add, bitvec_toNat_shift_add 111 (h := by trivial),
        Normalize.normalize_3_shift_111_add, bitvec_toNat_shift_add 120 (h := by trivial),
        Normalize.normalize_3_shift_120_add, bitvec_toNat_shift_add 129 (h := by trivial),
        Normalize.normalize_3_shift_129_add, bitvec_toNat_shift_add 138 (h := by trivial),
        Normalize.normalize_3_shift_138_add, bitvec_toNat_shift_add 147 (h := by trivial),
        Normalize.normalize_3_shift_147_add, bitvec_toNat_shift_add 156 (h := by trivial),
        Normalize.normalize_3_shift_156_add, bitvec_toNat_shift_add 165 (h := by trivial),
        Normalize.normalize_3_shift_165_add, bitvec_toNat_shift_add 174 (h := by trivial),
        Normalize.normalize_3_shift_174_add, bitvec_toNat_shift_add 183 (h := by trivial),
        Normalize.normalize_3_shift_183_add, bitvec_toNat_shift_add 192 (h := by trivial),
        Normalize.normalize_unpacked_toNat,
        bitvec_toNat_shift_add 18 (h := by trivial),
        bitvec_toNat_shift_add 27 (h := by trivial),
        bitvec_toNat_shift_add 36 (h := by trivial),
        bitvec_toNat_shift_add 45 (h := by trivial),
        bitvec_toNat_shift_add 54 (h := by trivial),
        bitvec_toNat_shift_add 63 (h := by trivial),
        bitvec_toNat_shift_add 72 (h := by trivial),
        bitvec_toNat_shift_add 81 (h := by trivial),
        bitvec_toNat_shift_add 90 (h := by trivial),
        bitvec_toNat_shift_add 99 (h := by trivial),
        bitvec_toNat_shift_add 108 (h := by trivial),
        bitvec_toNat_shift_add 117 (h := by trivial),
        bitvec_toNat_shift_add 126 (h := by trivial),
        bitvec_toNat_shift_add 135 (h := by trivial),
        bitvec_toNat_shift_add 144 (h := by trivial),
        bitvec_toNat_shift_add 153 (h := by trivial),
        bitvec_toNat_shift_add 162 (h := by trivial),
        bitvec_toNat_shift_add 171 (h := by trivial),
        bitvec_toNat_shift_add 180 (h := by trivial),
        bitvec_toNat_shift_add 189 (h := by trivial),
        bitvec_toNat_shift_add 192 (h := by trivial),
        Normalize.normalize_unpacked_toNat,
        ←BitVec.toNat_eq
      ]
      simp only [keccak_constants, Normalize.mask_bitvec, Nat.reduceMul]
      rewrite [BitVec.ofNat_toNat]
      bv_decide

  lemma os_theta {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P):
    (os c round i j).val = (s c round i j).val + (
      Normalize.normalize_unpacked (
        (s c round (i+4) 0).val +
        (s c round (i+4) 1).val +
        (s c round (i+4) 2).val +
        (s c round (i+4) 3).val +
        (s c round (i+4) 4).val
      ) 64 +
      ((BitVec.ofNat 192
              (Normalize.normalize_unpacked
                ((s c round (i+1) 0).val + (s c round (i+1) 1).val + (s c round (i+1) 2).val + (s c round (i+1) 3).val +
                  (s c round (i+1) 4).val)
                64)).rotateLeft
          BIT_COUNT).toNat
    )
  := by
    unfold os t
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    simp [ZMod.val_add, -BitVec.toNat_rotateLeft]
    rewrite [decode_bc h_meets_constraints h_round h_P (i+4)]
    simp [keccak_constants, get_rotate_count, -BitVec.toNat_rotateLeft]
    rewrite [decode_bc_rotated h_meets_constraints h_round h_P (i+1)]
    simp [keccak_constants, ZMod.val_add, -BitVec.toNat_rotateLeft]
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . have := s_range h_meets_constraints h_round (by omega) (i := (i+4)) (j := 0)
      have := s_range h_meets_constraints h_round (by omega) (i := (i+4)) (j := 1)
      have := s_range h_meets_constraints h_round (by omega) (i := (i+4)) (j := 2)
      have := s_range h_meets_constraints h_round (by omega) (i := (i+4)) (j := 3)
      have := s_range h_meets_constraints h_round (by omega) (i := (i+4)) (j := 4)
      simp_all [Normalize.mask]
      omega
    . have h_s := s_range h_meets_constraints h_round (by omega) (i := i) (j := j)
      have h_norm (x: ℕ) := Normalize.normalize_unpacked_64_le_mask (x := x)
      simp_all only [Normalize.mask]
      apply lt_of_lt_of_le _ h_P
      have h_bv (x: BitVec 192) : x.toNat ≤ 2^192-1 := by omega
      apply lt_of_le_of_lt (add_le_add h_s (add_le_add (h_norm _) (h_bv _)))
      norm_num


end Keccak.Soundness

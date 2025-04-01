import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Theta
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Bc
import Examples.Scroll.Keccak.Soundness.Lookups
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

  lemma os_eq_theta_s {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_equiv: s_equiv (s c round) state h_state_size) (h_P: P ≥ 366):
    s_equiv (os c round) (LeanCrypto.HashFunctions.θ state) (theta_state_size h_state_size)
  := by
    unfold LeanCrypto.HashFunctions.θ os s_equiv
    have ne_zero: NeZero P := by
      constructor
      simp_all [Nat.Prime.ne_zero]
    intro i j
    simp only [θ_indexed_eval h_state_size]
    unfold s_equiv at h_equiv
    simp [ZMod.val_add, h_equiv i j]
    unfold t
    simp [bc.eq_def, Transform.split_expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known]
    simp [normalize_bc, *]
    simp [get_rotate_count, list_ops]
    unfold Decode.expr
    simp
    -- have h_output_row_1 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 1)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 121))
    -- simp at h_output_row_1; obtain ⟨lookup_row_1, h_lookup_row_1⟩ := h_output_row_1
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_1
    -- rewrite [h_lookup_row_1.2]
    -- have h_output_row_2 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 2)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 122))
    -- simp at h_output_row_2; obtain ⟨lookup_row_2, h_lookup_row_2⟩ := h_output_row_2
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_2
    -- rewrite [h_lookup_row_2.2]
    -- have h_output_row_3 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 3)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 123))
    -- simp at h_output_row_3; obtain ⟨lookup_row_3, h_lookup_row_3⟩ := h_output_row_3
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_3
    -- rewrite [h_lookup_row_3.2]
    -- have h_output_row_4 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 4)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 124))
    -- simp at h_output_row_4; obtain ⟨lookup_row_4, h_lookup_row_4⟩ := h_output_row_4
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_4
    -- rewrite [h_lookup_row_4.2]
    -- have h_output_row_5 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 5)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 125))
    -- simp at h_output_row_5; obtain ⟨lookup_row_5, h_lookup_row_5⟩ := h_output_row_5
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_5
    -- rewrite [h_lookup_row_5.2]
    -- have h_output_row_6 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 6)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 126))
    -- simp at h_output_row_6; obtain ⟨lookup_row_6, h_lookup_row_6⟩ := h_output_row_6
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_6
    -- rewrite [h_lookup_row_6.2]
    -- have h_output_row_7 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 7)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 127))
    -- simp at h_output_row_7; obtain ⟨lookup_row_7, h_lookup_row_7⟩ := h_output_row_7
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_7
    -- rewrite [h_lookup_row_7.2]
    -- have h_output_row_8 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 8)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 128))
    -- simp at h_output_row_8; obtain ⟨lookup_row_8, h_lookup_row_8⟩ := h_output_row_8
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_8
    -- rewrite [h_lookup_row_8.2]
    -- have h_output_row_9 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 9)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 129))
    -- simp at h_output_row_9; obtain ⟨lookup_row_9, h_lookup_row_9⟩ := h_output_row_9
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_9
    -- rewrite [h_lookup_row_9.2]
    -- have h_output_row_10 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 10)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 130))
    -- simp at h_output_row_10; obtain ⟨lookup_row_10, h_lookup_row_10⟩ := h_output_row_10
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_10
    -- rewrite [h_lookup_row_10.2]
    -- have h_output_row_11 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 11)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 131))
    -- simp at h_output_row_11; obtain ⟨lookup_row_11, h_lookup_row_11⟩ := h_output_row_11
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_11
    -- rewrite [h_lookup_row_11.2]
    -- have h_output_row_12 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 12)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 132))
    -- simp at h_output_row_12; obtain ⟨lookup_row_12, h_lookup_row_12⟩ := h_output_row_12
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_12
    -- rewrite [h_lookup_row_12.2]
    -- have h_output_row_13 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 13)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 133))
    -- simp at h_output_row_13; obtain ⟨lookup_row_13, h_lookup_row_13⟩ := h_output_row_13
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_13
    -- rewrite [h_lookup_row_13.2]
    -- have h_output_row_14 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 14)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 134))
    -- simp at h_output_row_14; obtain ⟨lookup_row_14, h_lookup_row_14⟩ := h_output_row_14
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_14
    -- rewrite [h_lookup_row_14.2]
    -- have h_output_row_15 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 15)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 135))
    -- simp at h_output_row_15; obtain ⟨lookup_row_15, h_lookup_row_15⟩ := h_output_row_15
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_15
    -- rewrite [h_lookup_row_15.2]
    -- have h_output_row_16 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 16)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 136))
    -- simp at h_output_row_16; obtain ⟨lookup_row_16, h_lookup_row_16⟩ := h_output_row_16
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_16
    -- rewrite [h_lookup_row_16.2]
    -- have h_output_row_17 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 17)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 137))
    -- simp at h_output_row_17; obtain ⟨lookup_row_17, h_lookup_row_17⟩ := h_output_row_17
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_17
    -- rewrite [h_lookup_row_17.2]
    -- have h_output_row_18 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 18)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 138))
    -- simp at h_output_row_18; obtain ⟨lookup_row_18, h_lookup_row_18⟩ := h_output_row_18
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_18
    -- rewrite [h_lookup_row_18.2]
    -- have h_output_row_19 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 19)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 139))
    -- simp at h_output_row_19; obtain ⟨lookup_row_19, h_lookup_row_19⟩ := h_output_row_19
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_19
    -- rewrite [h_lookup_row_19.2]
    -- have h_output_row_20 := h_bc_4''' 3 (cell_manager c round (96 + 22 * ↑(i+4) + 20)) 3 (cell_manager c round (96 + 22 * ↑(i+4) + 140))
    -- simp at h_output_row_20; obtain ⟨lookup_row_20, h_lookup_row_20⟩ := h_output_row_20
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_20
    -- rewrite [h_lookup_row_20.2]
    -- have h_output_row_21 := h_bc_4''' 1 (cell_manager c round (96 + 22 * ↑(i+4) + 21)) 1 (cell_manager c round (96 + 22 * ↑(i+4) + 141))
    -- simp at h_output_row_21; obtain ⟨lookup_row_21, h_lookup_row_21⟩ := h_output_row_21
    -- apply Lookups.Normalize_6.apply_transform_table at h_lookup_row_21
    -- rewrite [h_lookup_row_21.2]
    -- clear h_bc_4'''




    -- fin_cases i <;> simp [←List.map_take, ←List.map_drop]
    -- . rewrite [take_get_0 (by simp; omega) (by omega)]
    --   simp
    --   have := normalize_add_eq_xor (UInt64_to_unpacked_Nat state[↑j])
    --   rewrite [normalize_unpacked_UInt64] at this
    --   sorry
    -- . rewrite [take_get_5 (by simp_all; omega) (by simp_all; omega) (by omega)]
    --   simp
    --   rewrite [(Array.getElem?_eq_some_getElem_iff state _ (by omega)).mpr True.intro]
    --   simp
    --   sorry
    -- . rewrite [take_get_10 (by simp_all; omega) (by simp_all; omega) (by simp_all; omega) (by omega)]
    --   simp
    --   rewrite [(Array.getElem?_eq_some_getElem_iff state _ (by omega)).mpr True.intro]
    --   simp
    --   sorry
    -- . rewrite [take_get_15 (by simp_all; omega) (by simp_all; omega) (by simp_all; omega) (by simp_all; omega) (by omega)]
    --   simp
    --   rewrite [(Array.getElem?_eq_some_getElem_iff state _ (by omega)).mpr True.intro]
    --   simp
    --   sorry
    -- . rewrite [take_get_20 (by simp_all; omega) (by simp_all; omega) (by simp_all; omega) (by simp_all; omega) (by omega)]
    --   simp
    --   rewrite [(Array.getElem?_eq_some_getElem_iff state _ (by omega)).mpr True.intro]
    --   simp
    --   sorry


end Keccak.Soundness

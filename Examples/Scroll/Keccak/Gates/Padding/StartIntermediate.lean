import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.Padding
  lemma gate_139_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_139 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 0 = 1 →
    (input_bytes c round).1[0]? = .some (8, is_first_padding c round 0)
  := by
    unfold gate_139 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rewrite [hgate, sub_eq_add_neg, add_right_inj, neg_inj, Nat.sub_add_comm, Nat.add_mod_right]
    congr
    rewrite [Nat.mod_eq_of_lt, ←(@Nat.sub_add_cancel round 1), mul_add]
    simp
    exact hround_lower
    exact lt_trans (by trivial) h_n
    rewrite [Nat.mod_eq_of_lt]
    omega
    exact lt_trans (by trivial) h_n

  lemma gate_141_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_141 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 1 = 1 →
    (input_bytes c round).1[1]? = .some (8, is_first_padding c round 1)
  := by
    unfold gate_141 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

  lemma gate_143_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_143 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 2 = 1 →
    (input_bytes c round).1[2]? = .some (8, is_first_padding c round 2)
  := by
    unfold gate_143 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

  lemma gate_145_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_145 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 3 = 1 →
    (input_bytes c round).1[3]? = .some (8, is_first_padding c round 3)
  := by
    unfold gate_145 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

  lemma gate_147_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_147 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 4 = 1 →
    (input_bytes c round).1[4]? = .some (8, is_first_padding c round 4)
  := by
    unfold gate_147 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

  lemma gate_149_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_149 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 5 = 1 →
    (input_bytes c round).1[5]? = .some (8, is_first_padding c round 5)
  := by
    unfold gate_149 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

  lemma gate_151_padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_151 c) (h_n: 215 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_paddings c round 6 = 1 →
    (input_bytes c round).1[6]? = .some (8, is_first_padding c round 6)
  := by
    unfold gate_151 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

  lemma gate_153_padding_start_intermediate_byte_last_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_153 c) (h_n: 215 < c.n):
    ∀ round ≤ 16, round > 0 →
    is_paddings c round 7 = 1 →
    (input_bytes c round).1[7]? = .some (8, is_first_padding c round 7)
  := by
    unfold gate_153 at hgate
    intro round hround hround_lower h_is_padding
    replace hgate := hgate (12*round)
    have hround': round ≤ 17 := le_trans hround (by trivial)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.fixed_6_q_padding_last, Selectors.q_padding_at_round_start, hround', hround_lower, one_mul] at hgate
    have h_n': 12*round+11 < c.n := by omega
    simp [to_cell_manager, h_n'] at hgate
    simp [is_paddings] at h_is_padding
    have hround'': 12*round ≠ 204 := by omega
    have hround''': 12*round ≤ 311 := by omega
    simp [Selectors.q_padding_last, hround'', hround'''] at hgate
    rewrite [h_is_padding] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_zipIdx]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [cell_manager_to_raw, add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

end Keccak.Gates.Padding

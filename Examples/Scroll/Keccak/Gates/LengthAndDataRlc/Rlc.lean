import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Gates.Padding.IsPaddingBoolean
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Advice
import Examples.Scroll.Keccak.Spec.InputBytes
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.LengthAndDataRlc
  lemma gate_156_initial_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_156 c) (h_is_final_first: is_final_disabled_on_first_row c) (h_is_final_bool: boolean_is_final c) (h_n: 212 < c.n):
    ∀ round ≤ 17, round > 0 → (
      ((round = 1 ∨ is_final c (12*(round-1)) = 1) ∧ (
        data_rlc c (12*round + NUM_BYTES_PER_WORD) = 0
      )) ∨ (
        (round ≠ 1 ∧ is_final c (12*(round-1)) = 0) ∧ (
          data_rlc c (12*round + NUM_BYTES_PER_WORD) = data_rlc c (12*(round-1))
        )
      )
    ) := by
      unfold gate_156 at hgate
      unfold is_final_disabled_on_first_row at h_is_final_first
      unfold boolean_is_final at h_is_final_bool
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_1_q_first, Selectors.fixed_5_q_padding, to_named_advice] at hgate
      have h_n': 12 < c.n := lt_trans (by trivial) h_n
      have h_n'': 12 * round - 12 < c.n := lt_trans (
        @lt_of_le_of_lt _ _ _ 192 _ (
          by simp [Nat.mul_le_mul (le_of_eq (by trivial)) hround]
        ) (by trivial)
      ) h_n
      have h_n''': 20 < c.n := lt_trans (by trivial) h_n
      have h_n'''': 12*round + 8 < c.n := lt_of_le_of_lt (
        Nat.add_le_add_right (Nat.mul_le_mul_left 12 hround) 8
      ) h_n
      simp [keccak_constants]
      rewrite [Nat.sub_add_comm, Nat.add_mod_right, Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_involutive] at hgate
      . rewrite [Nat.mod_eq_of_lt h_n', Nat.mod_eq_of_lt h_n''] at hgate
        if hround1: round = 1 then {
          simp_all [Selectors.q_first_zero, Nat.mod_eq_of_lt]
        } else {
          simp_all [Nat.mul_sub]
          have h_q_first: Selectors.q_first c (12*round - 12) = 0 := by
            unfold Selectors.q_first
            rw [ite_cond_eq_false, ite_cond_eq_true]
            . simp; omega
            . simp; match round with | 0 | 1 => contradiction | x+2 => simp [mul_add]
          if h_is_final: is_final c (12*round - 12) = 0 then {
            right
            simp_all [Nat.mod_eq_of_lt]
          } else {
            left
            have h_is_final: is_final c (12*round - 12) = 1 := by
              replace h_is_final_bool := h_is_final_bool (round-1)
              have hround': round ≤ 26 := le_trans hround (by trivial)
              simp_all [Nat.mul_sub]
            simp_all [Nat.mod_eq_of_lt]
          }
        }
      . rewrite [Nat.mod_eq_of_lt h_n']
        omega

  lemma gate_157_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_157 c) (h_is_padding_bool: gate_129 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 0 = 0 ∧ data_rlc c (12*round + 7) = data_rlc c (12*round + 8) * c.get_challenge 1 0 + get_input_byte_expr c round 0) ∨
      (is_paddings c round 0 = 1 ∧ data_rlc c (12*round + 7) = data_rlc c (12*round + 8))
    ) := by
      unfold gate_157 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_129_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 7 < c.n := by omega
      have h_n'': 12*round + 8 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice, ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, to_cell_manager, Nat.mod_eq_of_lt, h_n', h_n'', h_n'''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_0]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_158_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_158 c) (h_is_padding_bool: gate_130 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 1 = 0 ∧ data_rlc c (12*round + 6) = data_rlc c (12*round + 7) * c.get_challenge 1 0 + get_input_byte_expr c round 1) ∨
      (is_paddings c round 1 = 1 ∧ data_rlc c (12*round + 6) = data_rlc c (12*round + 7))
    ) := by
      unfold gate_158 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_130_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 6 < c.n := by omega
      have h_n'': 12*round + 7 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice, ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, to_cell_manager, Nat.mod_eq_of_lt, h_n', h_n'', h_n'''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_1]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_159_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_159 c) (h_is_padding_bool: gate_131 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 2 = 0 ∧ data_rlc c (12*round + 5) = data_rlc c (12*round + 6) * c.get_challenge 1 0 + get_input_byte_expr c round 2) ∨
      (is_paddings c round 2 = 1 ∧ data_rlc c (12*round + 5) = data_rlc c (12*round + 6))
    ) := by
      unfold gate_159 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_131_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 5 < c.n := by omega
      have h_n'': 12*round + 6 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice, ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, to_cell_manager, Nat.mod_eq_of_lt, h_n', h_n'', h_n'''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_2]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_160_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_160 c) (h_is_padding_bool: gate_132 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 3 = 0 ∧ data_rlc c (12*round + 4) = data_rlc c (12*round + 5) * c.get_challenge 1 0 + get_input_byte_expr c round 3) ∨
      (is_paddings c round 3 = 1 ∧ data_rlc c (12*round + 4) = data_rlc c (12*round + 5))
    ) := by
      unfold gate_160 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_132_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 4 < c.n := by omega
      have h_n'': 12*round + 5 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice, ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, to_cell_manager, Nat.mod_eq_of_lt, h_n', h_n'', h_n'''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_3]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_161_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_161 c) (h_is_padding_bool: gate_133 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 4 = 0 ∧ data_rlc c (12*round + 3) = data_rlc c (12*round + 4) * c.get_challenge 1 0 + get_input_byte_expr c round 4) ∨
      (is_paddings c round 4 = 1 ∧ data_rlc c (12*round + 3) = data_rlc c (12*round + 4))
    ) := by
      unfold gate_161 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_133_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 3 < c.n := by omega
      have h_n'': 12*round + 4 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice] at hgate
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding] at hgate
      simp [to_cell_manager, h_n'''] at hgate
      simp [Nat.mod_eq_of_lt, h_n', h_n''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_4]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_162_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_162 c) (h_is_padding_bool: gate_134 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 5 = 0 ∧ data_rlc c (12*round + 2) = data_rlc c (12*round + 3) * c.get_challenge 1 0 + get_input_byte_expr c round 5) ∨
      (is_paddings c round 5 = 1 ∧ data_rlc c (12*round + 2) = data_rlc c (12*round + 3))
    ) := by
      unfold gate_162 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_134_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 2 < c.n := by omega
      have h_n'': 12*round + 3 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice] at hgate
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding] at hgate
      simp [to_cell_manager, h_n'''] at hgate
      simp [Nat.mod_eq_of_lt, h_n', h_n''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_5]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_163_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_163 c) (h_is_padding_bool: gate_135 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 6 = 0 ∧ data_rlc c (12*round + 1) = data_rlc c (12*round + 2) * c.get_challenge 1 0 + get_input_byte_expr c round 6) ∨
      (is_paddings c round 6 = 1 ∧ data_rlc c (12*round + 1) = data_rlc c (12*round + 2))
    ) := by
      unfold gate_163 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_135_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round + 1 < c.n := by omega
      have h_n'': 12*round + 2 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice] at hgate
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding] at hgate
      simp [to_cell_manager, h_n'''] at hgate
      simp [Nat.mod_eq_of_lt, h_n', h_n''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_6]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

  lemma gate_164_intermediate_data_rlc (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_164 c) (h_is_padding_bool: gate_136 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 → (
      (is_paddings c round 7 = 0 ∧ data_rlc c (12*round) = data_rlc c (12*round + 1) * c.get_challenge 1 0 + get_input_byte_expr c round 7) ∨
      (is_paddings c round 7 = 1 ∧ data_rlc c (12*round) = data_rlc c (12*round + 1))
    ) := by
      unfold gate_164 at hgate
      intro round hround hround_lower
      replace hgate := hgate (12*round)
      replace h_is_padding_bool := Padding.gate_136_is_padding_boolean c h_fixed h_is_padding_bool h_n round (le_trans hround (by trivial))
      simp only [is_paddings] at h_is_padding_bool
      have h_n': 12*round < c.n := by omega
      have h_n'': 12*round + 1 < c.n := by omega
      have h_n''': 12*round + 11 < c.n := by omega
      simp [to_named_advice] at hgate
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding] at hgate
      simp [to_cell_manager, h_n'''] at hgate
      simp [Nat.mod_eq_of_lt, h_n', h_n''] at hgate
      rewrite [Selectors.q_padding_at_round_start c hround hround_lower, one_mul] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_add, neg_involutive, neg_involutive] at hgate
      cases h_is_padding_bool with
        | inl h_is_padding_zero =>
          left
          simp_all [is_paddings, get_input_byte_expr_7]
        | inr h_is_padding_one =>
          right
          simp_all [is_paddings]

end Keccak.Gates.LengthAndDataRlc

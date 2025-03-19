import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.Padding
  lemma gate_138_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_138 c) (h_n: 311 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 0 = 0 ∨
    is_first_padding c round 0 = 1
  := by
    unfold gate_138 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have h_5: 5 % c.n = 5 := Nat.mod_eq_of_lt (by omega)
    simp only [h_5] at hgate
    rewrite [Nat.sub_add_comm (by omega)] at hgate
    rewrite [Nat.add_mod_right] at hgate
    have h_12: 12*round - 5 = 12*(round-1) + 7 := by
      simp [Nat.mul_sub]
      rewrite [←Nat.sub_add_comm]
      simp
      omega
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [h_12, mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, Nat.reduceDiv, Nat.reduceMod, Nat.reduceAdd]
        rw [Nat.mod_eq_of_lt, hgate, sub_self]
        omega
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rw [Nat.mod_eq_of_lt]
        omega

  lemma gate_140_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_140 c) (h_n: 204 < c.n):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 1 = 0 ∨
    is_first_padding c round 1 = 1
  := by
    unfold gate_140 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
        rw [Nat.mod_eq_of_lt, sub_self]
        omega
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [hgate, is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rw [Nat.mod_eq_of_lt]
        omega

  lemma gate_142_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_142 c):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 2 = 0 ∨
    is_first_padding c round 2 = 1
  := by
    unfold gate_142 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, hgate, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rfl

  lemma gate_144_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_144 c):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 3 = 0 ∨
    is_first_padding c round 3 = 1
  := by
    unfold gate_144 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [hgate, is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rfl

  lemma gate_146_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_146 c):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 4 = 0 ∨
    is_first_padding c round 4 = 1
  := by
    unfold gate_146 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [hgate, is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rfl

  lemma gate_148_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_148 c):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 5 = 0 ∨
    is_first_padding c round 5 = 1
  := by
    unfold gate_148 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [hgate, is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rfl

  lemma gate_150_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_150 c):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 6 = 0 ∨
    is_first_padding c round 6 = 1
  := by
    unfold gate_150 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [hgate, is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rfl

  lemma gate_152_padding_step_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_152 c):
    ∀ round ≤ 17, round > 0 →
    is_first_padding c round 7 = 0 ∨
    is_first_padding c round 7 = 1
  := by
    unfold gate_152 at hgate
    intro round hround hround_lower
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, one_mul, hround, hround_lower] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    rewrite [mul_eq_zero] at hgate
    cases hgate with
      | inl hgate =>
        left
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, hgate]
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [hgate, is_first_padding, is_padding_prev, is_paddings, cell_manager_to_raw, sub_eq_add_neg]
        rfl
end Keccak.Gates.Padding

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.Padding
  lemma gate_129_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_129 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 0 = 0 ∨ is_paddings c round 0 = 1
  := by
    unfold gate_129 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_130_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_130 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 1 = 0 ∨ is_paddings c round 1 = 1
  := by
    unfold gate_130 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_131_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_131 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 2 = 0 ∨ is_paddings c round 2 = 1
  := by
    unfold gate_131 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_132_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_132 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 3 = 0 ∨ is_paddings c round 3 = 1
  := by
    unfold gate_132 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_133_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_133 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 4 = 0 ∨ is_paddings c round 4 = 1
  := by
    unfold gate_133 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_134_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_134 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 5 = 0 ∨ is_paddings c round 5 = 1
  := by
    unfold gate_134 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_135_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_135 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 6 = 0 ∨ is_paddings c round 6 = 1
  := by
    unfold gate_135 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

  lemma gate_136_is_padding_boolean (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_136 c) (h_n: 311 < c.n):
    ∀ round ≤ 25,
    is_paddings c round 7 = 0 ∨ is_paddings c round 7 = 1
  := by
    unfold gate_136 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, one_mul, Selectors.q_enable_at_round_start, hround] at hgate
    have h_n': (12*round)+11 < c.n := by linarith
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [to_cell_manager, h_n', zero_mul] at hgate
    cases hgate with
      | inl hgate => left; assumption
      | inr hgate =>
        right
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        rewrite [hgate]
        rfl

end Keccak.Gates.Padding

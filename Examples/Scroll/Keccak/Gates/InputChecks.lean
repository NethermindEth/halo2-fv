import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Advice
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.InputChecks
  lemma gate_125_boolean_is_final (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_125 c):
    boolean_is_final c
  := by
    unfold boolean_is_final
    intro round hround
    unfold gate_125 at hgate
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, Selectors.q_enable_at_round_start, hround, one_mul] at hgate
    simp only [to_named_advice] at hgate
    have no_zero_div := no_zero_divisors_zmod_p P_Prime
    simp [mul_eq_zero] at hgate
    cases hgate with
      | inl h => left; assumption
      | inr h =>
        right
        replace h := eq_neg_of_add_eq_zero_left h
        rewrite [neg_involutive] at h
        exact h.symm

end Keccak.Gates.InputChecks

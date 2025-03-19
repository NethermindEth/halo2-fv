import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.S
import Examples.Scroll.Keccak.Selectors

namespace Keccak

  namespace Gates

    namespace AbsorbVerifyInput
      lemma gate_100_absorb_verify_input (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_100 c):
        ∀ round, (round = 0 ∨ round = 25) →
          continue_hash c (12*round) → (
            absorb_from c (round+12) = s c round 1 2
          )
      := by
        unfold gate_100 at hgate
        intro round hround hcontinue_hash
        replace hgate := hgate (12*round)
        simp only [ValidCircuit.get_fixed, h_fixed, Selectors.q_absorb_at_start_or_end, hround, one_mul] at hgate
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        rewrite [mul_eq_zero] at hgate
        cases hgate with
          | inl h_start_new_hash =>
            unfold continue_hash start_new_hash at hcontinue_hash
            have ⟨hq_absorb, his_final⟩ := not_or.mp hcontinue_hash
            cases hround with
              | inl hround =>
                simp only [hround, Nat.reduceMul, ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1, ite_cond_eq_true] at hq_absorb
                contradiction
              | inr hround =>
                simp [hround, is_final] at his_final
                simp [hround, fixed_func, fixed_func_col_1] at h_start_new_hash
                replace h_start_new_hash := eq_neg_of_add_eq_zero_left h_start_new_hash
                rewrite [neg_involutive] at h_start_new_hash
                rewrite [h_start_new_hash] at his_final
                contradiction
          | inr heq =>
            replace heq := eq_neg_of_add_eq_zero_left heq
            rewrite [neg_involutive] at heq
            unfold absorb_from s cell_manager ValidCircuit.get_advice_wrapped
            norm_num
            simp only [mul_add, Nat.reduceMul, add_assoc, Nat.reduceAdd]
            rewrite [heq]
            cases hround with
              | inl hround => simp only [hround, mul_zero, Nat.zero_mod]
              | inr hround => simp only [hround, Nat.reduceMul]

    end AbsorbVerifyInput

  end Gates

end Keccak

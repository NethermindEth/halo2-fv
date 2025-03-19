import Examples.Scroll.Keccak.Spec.Advice
import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.S

namespace Keccak
  namespace Gates
    namespace AbsorbStateCopy
      lemma gate_118_absorb_state_copy (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_118 c) (h_is_final_bool: boolean_is_final c) (h_is_final_first: is_final_disabled_on_first_row c) (h_n: 323 < c.n):
        ∀ round, (round = 0 ∨ round = 25) →
          (continue_hash c (12*round) ∧ s c round 3 4 = s c (round+1) 3 4) ∨
          (¬continue_hash c (12*round) ∧ s c (round+1) 3 4 = 0)
        := by
          unfold gate_118 at hgate
          intro round hround
          replace hgate := hgate (12*round)
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.q_absorb_at_start_or_end, hround, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_factor: 12*round+19 = 12*(round+1)+7 := by trivial
          have h_n': 12*round+11<c.n := by cases hround <;> omega
          have h_n'': 12*(round+1)+11<c.n := by cases hround <;> omega
          simp [h_factor, to_named_advice, to_cell_manager, h_n', h_n'', to_s] at hgate
          unfold continue_hash start_new_hash
          unfold is_final_disabled_on_first_row at h_is_final_first
          unfold boolean_is_final at h_is_final_bool
          replace h_is_final_bool := h_is_final_bool round
          cases hround with
            | inl hround =>
              simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_1]
            | inr hround =>
              simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_1, zmod_not_zero_eq_one]
              cases h_is_final_bool <;> simp_all [zmod_not_zero_eq_one]
    end AbsorbStateCopy
  end Gates
end Keccak

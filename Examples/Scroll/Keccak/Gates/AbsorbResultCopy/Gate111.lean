import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Spec.Absorb
import Examples.Scroll.Keccak.Spec.IsFinal
import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.S
import Examples.Scroll.Keccak.Selectors

namespace Keccak

  namespace Gates

    namespace AbsorbVerifyInput
      lemma gate_111_absorb_result_copy (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_111 c) (h_is_final_bool: boolean_is_final c) (h_is_final_first: is_final_disabled_on_first_row c) (h_n: 515 < c.n):
        ∀ round, (round = 0 ∨ round = 25) →
          ((continue_hash c (12*round) ∧ absorb_result c (round+17) = s c (round+1) 1 3) ∨
          ((¬continue_hash c (12*round)) ∧ absorb_data c (round+17) = s c (round+1) 1 3))
      := by
        unfold gate_111 at hgate
        intro round hround
        replace hgate := hgate (12*round)
        simp only [ValidCircuit.get_fixed, h_fixed, Selectors.q_absorb_at_start_or_end, hround, one_mul] at hgate
        have h_factor: 12*round+20 = 12*(round+1)+8 := by trivial
        have h_factor': 12*round+206 = 12*(round+17)+2 := by trivial
        have h_factor'': 12*round+207 = 12*(round+17)+3 := by trivial
        have h_n': 12*(round+1)+11 < c.n := by
          cases hround with
            | inl hround => simp [hround]; linarith
            | inr hround => simp [hround]; linarith
        have h_n'': 12*(round+17)+11 < c.n := by
          cases hround with
            | inl hround => simp [hround]; linarith
            | inr hround => simp [hround]; assumption
        simp [h_factor, h_factor', h_factor'', to_cell_manager, h_n', h_n'', to_s, to_absorb, to_is_final] at hgate
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        unfold boolean_is_final at h_is_final_bool
        unfold is_final_disabled_on_first_row at h_is_final_first
        replace h_is_final := h_is_final_bool round
        unfold continue_hash start_new_hash
        cases hround with
          | inl hround =>
            simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_1]
          | inr hround =>
            simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_1, zmod_not_zero_eq_one]
            cases h_is_final with
              | inl h_is_final => simp_all [zmod_not_zero_eq_one]
              | inr h_is_final => simp_all

    end AbsorbVerifyInput

  end Gates

end Keccak

import Examples.Scroll.Keccak.Spec.Decode
import Examples.Scroll.Keccak.Spec.IotaS
import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.S

namespace Keccak

  namespace Gates

    namespace NextRowCheck

      lemma gate_53_next_row_check (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_53 c) (h_n: 311 < c.n):
        ∀ round ≤ 23,
        iota_s c (round+1) 0 1 = s c (round+2) 0 1
      := by
        unfold gate_53 at hgate
        intro round h_round_range
        simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
        replace hgate := hgate (12*(round+1))
        rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        have h_row_range : (12 * (round+1)) + 11 < c.n := by omega
        have h_row_range_next: (12*((round+1)+1)) + 11 < c.n := by omega
        simp only [to_decode] at hgate
        simp [to_cell_manager, h_row_range] at hgate
        have h_next_round: (12 * (round + 1) + 13) % c.n = (12* ((round+1)+1) + 1) % c.n := by
          rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, mul_add, mul_add, mul_add] <;> omega
        simp [h_next_round, to_cell_manager, h_row_range_next] at hgate
        simp only [to_s, to_iota_s] at hgate
        exact hgate

    end NextRowCheck

  end Gates

end Keccak

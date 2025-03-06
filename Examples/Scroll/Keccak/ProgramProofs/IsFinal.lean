import Examples.Scroll.Keccak.Gates.IsFinal
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma is_final_eq_last_is_padding_of_meets_constraints (h: meets_constraints c):
    is_final_eq_last_is_padding c
  := by
    have h_n := n_range_of_meets_constraints h
    exact Gates.IsFinal.gate_127_is_final_eq_last_is_padding
      c
      (fixed_of_meets_constraints h)
      (gate_127_of_meets_constraints h)
      (by omega)

  lemma is_final_only_when_q_enable_of_meets_constraints (h: meets_constraints c):
    ∀ row ≤ 300, row ≥ 11 → is_final_only_when_q_enable c row
  := by
    have h_n := n_range_of_meets_constraints h
    exact Gates.IsFinal.gate_128_is_final_only_when_q_enable
      c
      (fixed_of_meets_constraints h)
      (gate_128_of_meets_constraints h)
      (by omega)
end Keccak.Proofs

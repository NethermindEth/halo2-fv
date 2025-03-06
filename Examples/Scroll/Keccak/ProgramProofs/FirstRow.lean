import Examples.Scroll.Keccak.Gates.FirstRow
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma is_final_disabled_on_first_row_of_meets_constraints (h: meets_constraints c):
    is_final_disabled_on_first_row c
  := by
    exact Gates.FirstRow.gate_126_is_final_disabled_on_first_row
      c
      (fixed_of_meets_constraints h)
      (gate_126_of_meets_constraints h)
end Keccak.Proofs

import Examples.Scroll.Keccak.Gates.InputChecks
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma boolean_is_final_of_meets_constraints (h: meets_constraints c):
    boolean_is_final c
  := by
    exact Gates.InputChecks.gate_125_boolean_is_final
      c
      (fixed_of_meets_constraints h)
      (gate_125_of_meets_constraints h)
end Keccak.Proofs

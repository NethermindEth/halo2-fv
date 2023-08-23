import Halo2Fv.TwoChip

namespace TwoChip

  def spec (c: Circuit P P_Prime) (x y z: ZMod P): Prop := (x + y) * z = c.Instance 0 0

  lemma advice_satisfies_spec_of_constraints (c: Circuit P P_Prime) : meets_constraints c → spec c (c.Advice 0 0) (c.Advice 0 1) (c.Advice 0 2) := by
    unfold meets_constraints
    unfold all_gates all_copy_constraints
    unfold gate_0 gate_1
    unfold copy_0 copy_1 copy_2 copy_3 copy_4
    intro ⟨hS, ⟨⟨hGate0, hGate1⟩, ⟨⟨hA_0_3, hA_1_3, hA_0_5, hA_1_5, hA_0_6⟩, _⟩⟩⟩
    have h: c.Selector 0 3 * (c.Advice 0 3 + c.Advice 1 3 - c.Advice 0 4) = 0 := hGate0 3
    rewrite [hS, selector_func, one_mul] at h
    have h': c.Selector 1 5 * (c.Advice 0 5 * c.Advice 1 5 - c.Advice 0 6) = 0 := hGate1 5
    rewrite [hS, selector_func, one_mul] at h'
    rewrite [hA_0_3, hA_1_3, sub_eq_zero] at h
    rewrite [hA_0_5, hA_1_5, hA_0_6, sub_eq_zero, ←h] at h'
    exact h'

  theorem spec_of_constraints (c: Circuit P P_Prime) : meets_constraints c → ∃ x y z: ZMod P, spec c x y z := by
    intro hConstraints
    exact ⟨c.Advice 0 0, c.Advice 0 1, c.Advice 0 2, advice_satisfies_spec_of_constraints c hConstraints⟩

  theorem instance_of_witness (c: Circuit P P_Prime) (hAdvice: c.Advice = advice_func c) :
    meets_constraints c → spec c c.a c.b c.c := by
      intro hConstraints
      have hSpec: spec c (c.Advice 0 0) (c.Advice 0 1) (c.Advice 0 2) := advice_satisfies_spec_of_constraints c hConstraints
      aesop

end TwoChip
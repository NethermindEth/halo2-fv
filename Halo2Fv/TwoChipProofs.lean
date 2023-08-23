import Halo2Fv.TwoChip

namespace TwoChip

  lemma advice_satisfies_spec_of_constraints (c: Circuit P P_Prime) : meets_constraints c → spec c (c.Advice 0 0) (c.Advice 0 1) (c.Advice 0 2) := by
    unfold meets_constraints
    unfold all_selectors all_gates all_copy_constraints
    unfold selector_0_3 selector_0_n selector_1_5 selector_1_n
    unfold gate_0 gate_1
    unfold copy_0 copy_1 copy_2 copy_3 copy_4
    intro ⟨
      ⟨hS_0_3, _, hS_1_5, _⟩,
      ⟨
        ⟨hGate0, hGate1⟩,
        ⟨hAdvice_0_3, hAdvice_1_3, hAdvice_0_5, hAdvice_1_5, hAdvice_0_6⟩
      ⟩
    ⟩
    have h: c.Selector 0 3 * (c.Advice 0 3 + c.Advice 1 3 - c.Advice 0 4) = 0 := hGate0 3
    rewrite [hS_0_3, one_mul] at h
    have h': c.Selector 1 5 * (c.Advice 0 5 * c.Advice 1 5 - c.Advice 0 6) = 0 := hGate1 5
    rewrite [hS_1_5, one_mul] at h'
    rewrite [hAdvice_0_3, hAdvice_1_3, sub_eq_zero] at h
    rewrite [hAdvice_0_5, hAdvice_1_5, hAdvice_0_6, sub_eq_zero, ←h] at h'
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
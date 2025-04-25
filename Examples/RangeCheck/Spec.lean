import Examples.RangeCheck.Extraction
import Examples.Util

namespace RangeCheck

  example {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) :
    (c.get_advice 0 0 = 9) ∨
    (c.get_advice 0 0 = 8) ∨
    (c.get_advice 0 0 = 7) ∨
    (c.get_advice 0 0 = 6) ∨
    (c.get_advice 0 0 = 5) ∨
    (c.get_advice 0 0 = 4) ∨
    (c.get_advice 0 0 = 3) ∨
    (c.get_advice 0 0 = 2) ∨
    (c.get_advice 0 0 = 1) ∨
    (c.get_advice 0 0 = 0)
  := by
    unfold meets_constraints at h_meets_constraints
    have ⟨_,_,h_selector,_,_,_,h_gate,_,_,_,_⟩ := h_meets_constraints
    clear h_meets_constraints
    unfold all_gates gate_0 at h_gate
    unfold selector_func selector_func_col_0 at h_selector
    specialize h_gate 0
    simp [ValidCircuit.get_selector, h_selector] at h_gate
    have : NoZeroDivisors (ZMod P) := no_zero_divisors_zmod_p P_Prime
    have (a b: ZMod P) : a + -b = a - b := by simp [sub_eq_add_neg]
    simp [this] at h_gate
    have (a b: ZMod P) (h: a - b = 0): a = b := eq_of_sub_eq_zero h
    cases h_gate with
      | inl h_gate => right; cases h_gate with
        | inl h_gate => right; cases h_gate with
          | inl h_gate => right; cases h_gate with
            | inl h_gate => right; cases h_gate with
              | inl h_gate => right; cases h_gate with
                | inl h_gate => right; cases h_gate with
                  | inl h_gate => right; cases h_gate with
                    | inl h_gate => right; cases h_gate with
                      | inl h_gate => right; assumption
                      | inr h_gate => left; apply this at h_gate; rw [h_gate]
                    | inr h_gate => left; apply this at h_gate; rw [h_gate]
                  | inr h_gate => left; apply this at h_gate; rw [h_gate]
                | inr h_gate => left; apply this at h_gate; rw [h_gate]
              | inr h_gate => left; apply this at h_gate; rw [h_gate]
            | inr h_gate => left; apply this at h_gate; rw [h_gate]
          | inr h_gate => left; apply this at h_gate; rw [h_gate]
        | inr h_gate => left; apply this at h_gate; rw [h_gate]
      | inr h_gate => left; apply this at h_gate; rw [h_gate]


end RangeCheck

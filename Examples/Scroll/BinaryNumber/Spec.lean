import Examples.Scroll.BinaryNumber.Extraction
import Mathlib.Data.ZMod.Basic
import Examples.Util

namespace BinaryNumber

def spec (c: ValidCircuit P P_Prime): Prop :=
  ∀ row: ℕ, c.get_fixed 0 row = 1 → (
    (c.get_fixed 1 row = 0 ∧ c.get_advice 0 row = 0 ∧ c.get_advice 1 row = 0) ∨
    (c.get_fixed 1 row = 1 ∧ c.get_advice 0 row = 0 ∧ c.get_advice 1 row = 1) ∨
    (c.get_fixed 1 row = 2 ∧ c.get_advice 0 row = 1 ∧ c.get_advice 1 row = 0)
  )

theorem spec_of_meets_constraints (c: ValidCircuit P P_Prime): meets_constraints c → spec c := by
  unfold meets_constraints all_gates
  intro ⟨
    _, _, _, _, _, _, h_gates,
    _, _, _, _
  ⟩
  unfold gate_0 gate_1 gate_2 gate_3 at h_gates
  unfold spec
  intro row h_fixed
  have ⟨h_gate_0, h_gate_1, h_gate_2, h_gate_3⟩ := h_gates
  specialize h_gate_0 row
  specialize h_gate_1 row
  specialize h_gate_2 row
  specialize h_gate_3 row
  simp only [zero_mul, add_zero, one_mul, h_fixed] at h_gate_0 h_gate_1 h_gate_2 h_gate_3

  have no_zer_div := no_zero_divisors_zmod_p P_Prime

  have at_least_one_zero : c.get_advice 0 row = 0 ∨ c.get_advice 1 row = 0 := by
    exact mul_eq_zero.mp h_gate_3

  cases at_least_one_zero with
    | inl h_zero =>
      simp only [h_zero, neg_zero, add_zero, mul_one, mul_eq_zero, zero_mul, and_true, true_and] at h_gate_0 h_gate_1 h_gate_2 h_gate_3
      cases h_gate_1 with
        | inl h_zero1 =>
          simp only [h_zero1, neg_zero, add_zero, true_or, zero_add, neg_eq_zero, true_and] at h_gate_0 h_gate_2 h_gate_3
          aesop
        | inr h_one1 =>
          rw [add_neg_eq_zero] at h_gate_2 h_one1
          rw [←h_gate_2, ←h_one1]
          right
          left
          simp only [h_one1, h_gate_2, h_zero, and_self]
    | inr h_zero =>
      simp only [mul_eq_zero, h_zero, neg_zero, add_zero, mul_one, zero_add, mul_zero, and_true, true_and] at h_gate_0 h_gate_1 h_gate_2 h_gate_3
      cases h_gate_0 with
        | inl h_zero0 =>
          simp only [h_zero0, neg_zero, add_zero, true_or, zero_mul, zero_add, neg_eq_zero, true_and] at h_gate_2 ⊢
          simp only [h_gate_2, true_and]
          left
          assumption
        | inr h_one0 =>
          rw [add_neg_eq_zero] at h_one0
          rw [←h_one0] at h_gate_2 ⊢
          right
          right
          simp only [one_mul, add_neg_eq_zero] at h_gate_2
          aesop

end BinaryNumber

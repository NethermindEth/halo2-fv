import Examples.BinaryNumber
import Mathlib.Data.ZMod.Basic

namespace BinaryNumber

def spec (c: ValidCircuit P P_Prime): Prop :=
  ∀ row: ℕ, c.get_fixed 0 row = 1 → (
    (c.get_fixed 1 row = 0 ∧ c.get_advice 0 row = 0 ∧ c.get_advice 1 row = 0) ∨
    (c.get_fixed 1 row = 1 ∧ c.get_advice 0 row = 0 ∧ c.get_advice 1 row = 1) ∨
    (c.get_fixed 1 row = 2 ∧ c.get_advice 0 row = 1 ∧ c.get_advice 1 row = 0)
  )

lemma no_zero_divisors_zmod_p {P: ℕ} (P_Prime: Nat.Prime P): NoZeroDivisors (ZMod P) := by
  have fact_prime : Fact P.Prime := by simp [fact_iff, P_Prime]
  refine IsDomain.to_noZeroDivisors (ZMod P)

theorem spec_of_meets_constraints (c: ValidCircuit P P_Prime): meets_constraints c → spec c := by
  unfold meets_constraints all_gates
  intro ⟨
    _, _, _, _, _, _, h_gates,
    _, _, _, _
  ⟩
  unfold gate_0_0_ gate_1_0_ gate_2_0_ gate_3_0_ at h_gates
  unfold spec
  intro row h_fixed
  have h_gate_row := h_gates row
  simp only [zero_mul, add_zero, one_mul, h_fixed] at h_gate_row

  have no_zer_div := no_zero_divisors_zmod_p P_Prime

  have at_least_one_zero : c.get_advice 0 row = 0 ∨ c.get_advice 1 row = 0 := by
    have ⟨_, _, _, h⟩ := h_gate_row
    exact mul_eq_zero.mp h

  cases at_least_one_zero with
    | inl h_zero =>
      simp only [h_zero, neg_zero, add_zero, mul_one, mul_eq_zero, zero_mul, and_true, true_and] at h_gate_row
      have ⟨h_range, h_eq⟩ := h_gate_row
      cases h_range with
        | inl h_zero1 =>
          simp only [h_zero1, neg_zero, add_zero, true_or, zero_add, neg_eq_zero, true_and] at h_gate_row
          aesop
        | inr h_one1 =>
          rw [add_neg_eq_zero] at h_eq h_one1
          rw [←h_eq, ←h_one1]
          right
          left
          simp only [h_one1, h_eq, h_zero, and_self]
    | inr h_zero =>
      simp only [mul_eq_zero, h_zero, neg_zero, add_zero, mul_one, zero_add, mul_zero, and_true, true_and] at h_gate_row
      have ⟨h_range, h_eq⟩ := h_gate_row
      cases h_range with
        | inl h_zero0 =>
          simp only [h_zero0, neg_zero, add_zero, true_or, zero_mul, zero_add, neg_eq_zero, true_and] at h_gate_row h_eq ⊢
          simp only [h_eq, true_and]
          left
          assumption
        | inr h_one0 =>
          rw [add_neg_eq_zero] at h_one0
          rw [←h_one0] at h_eq h_gate_row ⊢
          right
          right
          simp only [one_mul, add_neg_eq_zero] at h_eq
          aesop

end BinaryNumber

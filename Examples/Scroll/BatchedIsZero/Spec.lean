import Examples.Scroll.BatchedIsZero.Extraction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Fib.Basic
import Examples.Util

namespace BatchedIsZero

def spec (c: ValidCircuit P P_Prime): Prop :=
  (c.get_advice 0 0 = 0 ∧ c.get_advice 1 0 = 0 ∧ c.get_advice 2 0 = 0 ∧ c.get_advice 4 0 = 1) ∨
  (¬(c.get_advice 0 0 = 0 ∧ c.get_advice 1 0 = 0 ∧ c.get_advice 2 0 = 0) ∧ c.get_advice 4 0 = 0)

lemma ne_zero_of_mul_eq_one {P: ℕ} {a b: ZMod P} (P_Prime: Nat.Prime P): 1 = a * b → a ≠ 0 ∧ b ≠ 0 := by
  intro h
  have h_contr: (1: ZMod P) ≠ (0: ZMod P) := zmod_p_one_neq_zero P_Prime
  aesop

theorem spec_of_meets_constraints (c: ValidCircuit P P_Prime): meets_constraints c → spec c := by
  unfold spec
  unfold meets_constraints all_gates
  intro ⟨
    h1, h2, h_selector, h4, h5, h6, h_gates,
    h8, h9, h10, h11
  ⟩
  have ⟨h_gate_0, h_gate_1, h_gate_2, h_gate_3, h_gate_4, h_gate_5⟩ := h_gates
  unfold gate_0 at h_gate_0
  unfold selector_func selector_func_col_0 at h_selector
  unfold ValidCircuit.get_selector at h_gate_0
  rw [h_selector] at h_gate_0
  simp only [zero_lt_one, ↓reduceIte, one_mul] at h_gate_0


  unfold gate_1 ValidCircuit.get_selector at h_gate_1
  rw [h_selector] at h_gate_1
  simp only [zero_lt_one, ↓reduceIte, one_mul] at h_gate_1


  unfold gate_2 ValidCircuit.get_selector at h_gate_2
  rw [h_selector] at h_gate_2
  simp only [zero_lt_one, ↓reduceIte, one_mul] at h_gate_2


  unfold gate_3 ValidCircuit.get_selector at h_gate_3
  rw [h_selector] at h_gate_3
  simp only [zero_lt_one, ↓reduceIte, one_mul] at h_gate_3


  unfold gate_4 ValidCircuit.get_selector at h_gate_4
  rw [h_selector] at h_gate_4
  simp only [zero_lt_one, ↓reduceIte, one_mul] at h_gate_4

  unfold gate_5 ValidCircuit.get_selector at h_gate_5
  rw [h_selector] at h_gate_5
  simp only [zero_lt_one, ↓reduceIte, one_mul, add_neg_eq_zero] at h_gate_5

  have no_zer_div := no_zero_divisors_zmod_p P_Prime

  specialize h_gate_0 0
  specialize h_gate_1 0
  specialize h_gate_2 0
  specialize h_gate_3 0
  specialize h_gate_4 0

  cases eq_zero_or_neZero (c.get_advice 4 0) with
  | inl h_4_zero =>
    simp [h_4_zero, mul_eq_zero] at h_gate_0 h_gate_1 h_gate_2 h_gate_3 h_gate_4
    cases h_gate_4 with
      | inl h => cases h with
        | inl h =>
          simp only [add_neg_eq_zero] at h
          have ⟨h1, _⟩ := ne_zero_of_mul_eq_one P_Prime h
          simp [h1, h_4_zero]
        | inr h =>
          simp only [add_neg_eq_zero] at h
          have ⟨h1, _⟩ := ne_zero_of_mul_eq_one P_Prime h
          simp [h1, h_4_zero]
      | inr h =>
        simp only [add_neg_eq_zero] at h
        have ⟨h1, _⟩ := ne_zero_of_mul_eq_one P_Prime h
        simp [h1, h_4_zero]
  | inr h =>
    left
    aesop (config := {warnOnNonterminal := false})
    simp only [add_neg_eq_zero] at h_1
    simp [h_1]

end BatchedIsZero

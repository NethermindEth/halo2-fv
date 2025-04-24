import Examples.Fibonacci.Extraction
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Fib.Basic


namespace Fibonacci.Ex1

def spec (c: ValidCircuit P P_Prime): Prop :=
  ∀ n: ℕ,
    (c.get_instance 0 0 = Nat.fib n ∧ c.get_instance 0 1 = Nat.fib (n+1)) →
    c.get_instance 0 2 = Nat.fib (n + 9)

def sum_row (c: ValidCircuit P P_Prime) (row: ℕ): Prop :=
  c.get_advice 2 row = c.get_advice 0 row + c.get_advice 1 row

lemma sum_row_of_meets_constraints (c: ValidCircuit P P_Prime): meets_constraints c → row < 8 → sum_row c row := by
  intro ⟨_, _, h_selector, _, _, _, h_gate, _, _, _, _⟩
  intro h_row
  unfold sum_row
  unfold all_gates gate_0 at h_gate
  unfold selector_func at h_selector
  have h_gate_row := h_gate row
  unfold ValidCircuit.get_selector at h_gate_row
  rewrite [h_selector] at h_gate_row
  dsimp only at h_gate_row
  unfold selector_func_col_0 at h_gate_row
  simp only [h_row, ite_true, one_mul] at h_gate_row
  generalize c.get_advice 0 row + c.get_advice 1 row = x at h_gate_row
  rewrite [add_eq_zero_iff_eq_neg', neg_eq_iff_eq_neg] at h_gate_row
  rewrite [h_gate_row]
  simp only [neg_neg]

theorem spec_of_meets_contraints (c: ValidCircuit P P_Prime): meets_constraints c → spec c := by
  unfold spec
  intro h_constraints
  have h_sums: ∀ row, row < 8 → sum_row c row := by
    intro row
    exact sum_row_of_meets_constraints c h_constraints
  revert h_constraints
  unfold meets_constraints all_copy_constraints copy_0_to_9 copy_0 copy_1 copy_2 copy_3 copy_4 copy_5 copy_6 copy_7 copy_8 copy_9 copy_10 copy_11 copy_12 copy_13 copy_14 copy_15 copy_16
  intro ⟨
    _, _, _, _, _, _, _,
    ⟨
      ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9⟩,
      ⟨hc10, hc11, hc12, hc13, hc14, hc15, hc16⟩
    ⟩,
    _, _, _
  ⟩
  intro n
  intro ⟨hfib1, hfib2⟩
  rw [←hc16]
  rw [←hc0] at hfib1
  rw [←hc1] at hfib2
  unfold sum_row at h_sums
  have h_row0 : c.get_advice 2 0 = ↑(Nat.fib (n+2)) := by
    rw [h_sums, hfib1, hfib2, Nat.fib_add_two]
    simp only [Nat.cast_add]
    trivial
  have h_row1 : c.get_advice 2 1 = ↑(Nat.fib (n+3)) := by
    rw [h_sums, hc2, hc3, hfib2, h_row0, ←Nat.cast_add, (@Nat.fib_add_two (n+1))]
    trivial
  have h_row2 : c.get_advice 2 2 = ↑(Nat.fib (n+4)) := by
    rw [h_sums, hc4, hc5, h_row0, h_row1, ←Nat.cast_add, (@Nat.fib_add_two (n+2))]
    trivial
  have h_row3 : c.get_advice 2 3 = ↑(Nat.fib (n+5)) := by
    rw [h_sums, hc6, hc7, h_row1, h_row2, ←Nat.cast_add, (@Nat.fib_add_two (n+3))]
    trivial
  have h_row4 : c.get_advice 2 4 = ↑(Nat.fib (n+6)) := by
    rw [h_sums, hc8, hc9, h_row2, h_row3, ←Nat.cast_add, (@Nat.fib_add_two (n+4))]
    trivial
  have h_row5 : c.get_advice 2 5 = ↑(Nat.fib (n+7)) := by
    rw [h_sums, hc10, hc11, h_row3, h_row4, ←Nat.cast_add, (@Nat.fib_add_two (n+5))]
    trivial
  have h_row6 : c.get_advice 2 6 = ↑(Nat.fib (n+8)) := by
    rw [h_sums, hc12, hc13, h_row4, h_row5, ←Nat.cast_add, (@Nat.fib_add_two (n+6))]
    trivial
  rw [h_sums, hc14, hc15, h_row5, h_row6, ←Nat.cast_add, (@Nat.fib_add_two (n+7))]
  trivial

end Fibonacci.Ex1

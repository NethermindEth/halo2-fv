import Examples.Fib2
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Fib.Basic

namespace Fibonacci.Ex2

def spec (c: ValidCircuit P P_Prime): Prop :=
  ∀ n: ℕ,
    (c.get_instance 0 0 = Nat.fib n ∧ c.get_instance 0 1 = Nat.fib (n+1)) →
    c.get_instance 0 2 = Nat.fib (n+11)

theorem spec_of_meets_constraints (c: ValidCircuit P P_Prime): meets_constraints c → spec c := by
  unfold spec
  intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  intro n
  unfold all_copy_constraints

end Fibonacci.Ex2

import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Fibonacci9

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P} (c: Circuit P P_Prime)
def copy_0: Prop := c.Advice 0 0 = c.Instance 0 0
def copy_1: Prop := c.Advice 1 0 = c.Instance 0 1
def copy_2: Prop := c.Advice 0 1 = c.Advice 1 0
def copy_3: Prop := c.Advice 1 1 = c.Advice 2 0
def copy_4: Prop := c.Advice 0 2 = c.Advice 2 0
def copy_5: Prop := c.Advice 1 2 = c.Advice 2 1
def copy_6: Prop := c.Advice 0 3 = c.Advice 2 1
def copy_7: Prop := c.Advice 1 3 = c.Advice 2 2
def copy_8: Prop := c.Advice 0 4 = c.Advice 2 2
def copy_9: Prop := c.Advice 1 4 = c.Advice 2 3
def copy_10: Prop := c.Advice 0 5 = c.Advice 2 3
def copy_11: Prop := c.Advice 1 5 = c.Advice 2 4
def copy_12: Prop := c.Advice 0 6 = c.Advice 2 4
def copy_13: Prop := c.Advice 1 6 = c.Advice 2 5
def copy_14: Prop := c.Advice 0 7 = c.Advice 2 5
def copy_15: Prop := c.Advice 1 7 = c.Advice 2 6
def copy_16: Prop := c.Advice 2 7 = c.Instance 0 2
def all_copy_constraints: Prop := copy_0 c ∧ copy_1 c ∧ copy_2 c ∧ copy_3 c ∧ copy_4 c ∧ copy_5 c ∧ copy_6 c ∧ copy_7 c ∧ copy_8 c ∧ copy_9 c ∧ copy_10 c ∧ copy_11 c ∧ copy_12 c ∧ copy_13 c ∧ copy_14 c ∧ copy_15 c ∧ copy_16 c
def all_fixed: Prop := true
def selector_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => 1
    | 0, 3 => 1
    | 0, 4 => 1
    | 0, 5 => 1
    | 0, 6 => 1
    | 0, 7 => 1
    | _, _ => 0
def advice_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | 0, 0 => c.Instance 0 0
    | 0, 1 => c.Instance 0 1
    | 0, 2 => (c.Instance 0 0) + (c.Instance 0 1)
    | 0, 3 => (c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))
    | 0, 4 => ((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))
    | 0, 5 => ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))
    | 0, 6 => (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))
    | 0, 7 => (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))
    | 1, 0 => c.Instance 0 1
    | 1, 1 => (c.Instance 0 0) + (c.Instance 0 1)
    | 1, 2 => (c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))
    | 1, 3 => ((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))
    | 1, 4 => ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))
    | 1, 5 => (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))
    | 1, 6 => (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))
    | 1, 7 => ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))) + ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))))
    | 2, 0 => (c.Instance 0 0) + (c.Instance 0 1)
    | 2, 1 => (c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))
    | 2, 2 => ((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))
    | 2, 3 => ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))
    | 2, 4 => (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))
    | 2, 5 => (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))
    | 2, 6 => ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))) + ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))))
    | 2, 7 => ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))) + (((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))) + ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))))
    | _, _ => 0
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | _, _ => 0
------GATES-------
def gate_0: Prop := ∀ row : ℕ,  c.Selector 0 row * (c.Advice  0 (row) + c.Advice  1 (row) - c.Advice  2 (row)) = 0
def all_gates: Prop := gate_0 c
def meets_constraints: Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func
end Fibonacci9

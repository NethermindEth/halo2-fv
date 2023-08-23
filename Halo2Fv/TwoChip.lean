import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace TwoChip

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
  a: ZMod P
  b: ZMod P
  c: ZMod P

variable {P: ℕ} {P_Prime: Nat.Prime P} (c: Circuit P P_Prime)
def copy_0: Prop := c.Advice 0 3 = c.Advice 0 0
def copy_1: Prop := c.Advice 1 3 = c.Advice 0 1
def copy_2: Prop := c.Advice 0 5 = c.Advice 0 4
def copy_3: Prop := c.Advice 1 5 = c.Advice 0 2
def copy_4: Prop := c.Advice 0 6 = c.Instance 0 0
def all_copy_constraints: Prop := copy_0 c ∧ copy_1 c ∧ copy_2 c ∧ copy_3 c ∧ copy_4 c
def all_fixed: Prop := true
def selector_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | 0, 3 => 1
    | 1, 5 => 1
    | _, _ => 0
def advice_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | 0, 0 => c.a
    | 0, 1 => c.b
    | 0, 2 => c.c
    | 0, 3 => c.a
    | 0, 4 => (c.a) + (c.b)
    | 0, 5 => (c.a) + (c.b)
    | 0, 6 => ((c.a) + (c.b)) * (c.c)
    | 1, 3 => c.b
    | 1, 5 => c.c
    | _, _ => 0
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | _, _ => 0
------GATES-------
def gate_0: Prop := ∀ row : ℕ,  c.Selector 0 row * (c.Advice  0 (row) + c.Advice  1 (row) - c.Advice  0 (row + 1)) = 0
def gate_1: Prop := ∀ row : ℕ,  c.Selector 1 row * (c.Advice  0 (row) * c.Advice  1 (row) - c.Advice  0 (row + 1)) = 0
def all_gates: Prop := gate_0 c ∧ gate_1 c
def meets_constraints: Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func
end TwoChip

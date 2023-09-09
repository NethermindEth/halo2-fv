import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Zcash.CondSwap

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P} (c: Circuit P P_Prime)
def copy_0: Prop := c.Advice 0 1 = c.Advice 0 0
def all_copy_constraints: Prop := copy_0 c
def all_fixed: Prop := true
def selector_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | 0, 1 => 1
    | _, _ => 0
def advice_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | _, _ => 0
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | _, _ => 0
------GATES-------
def gate_0: Prop := ∀ row : ℕ,   c.Selector 0 row * (c.Advice  2 (row) - (c.Advice  4 (row) * c.Advice  1 (row) + (1 - c.Advice  4 (row)) * c.Advice  0 (row))) = 0
def gate_1: Prop := ∀ row : ℕ,   c.Selector 0 row * (c.Advice  3 (row) - (c.Advice  4 (row) * c.Advice  0 (row) + (1 - c.Advice  4 (row)) * c.Advice  1 (row))) = 0
def gate_2: Prop := ∀ row : ℕ,   c.Selector 0 row * (c.Advice  4 (row) * (1 - c.Advice  4 (row))) = 0
def all_gates: Prop := gate_0 c ∧ gate_1 c ∧ gate_2 c
def meets_constraints: Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func
end Zcash.CondSwap

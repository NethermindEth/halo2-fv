import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Zcash.DecomposeRunningSum

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P} (c: Circuit P P_Prime)
def copy_0: Prop := c.Advice 0 84 = c.Advice 0 0
def copy_1: Prop := c.Fixed 1 0 = c.Advice 0 83
def copy_2: Prop := c.Fixed 1 1 = c.Advice 0 167
def all_copy_constraints: Prop := copy_0 c ∧ copy_1 c ∧ copy_2 c
def selector_func_col_0 : ℕ → ZMod P :=
  λ row => match row with
    | _+167 => 0
    | _+84 => 1
    | _+83 => 0
    | _ => 1
def selector_func : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 row
    | _ => 0
def fixed_func_col_1 : ℕ → ZMod P :=
  λ row => match row with
    | _ => 0
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 1 => fixed_func_col_1 row
    | _ => 0
------GATES-------
def gate_0: Prop := ∀ row : ℕ,  c.Selector 0 row * ((((((((c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)) * (1 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) * (0x2 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) * (0x3 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) * (0x4 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) * (0x5 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) * (0x6 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) * (0x7 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 0x8)))) = 0
def all_gates: Prop := gate_0 c
def meets_constraints: Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func
end Zcash.DecomposeRunningSum

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
--REGION: load private
--Annotation: private input
def advice_0_0: Prop := c.Advice 0 0 = c.a
--EXITED REGION: load private
--REGION: load private
--Annotation: private input
def advice_0_1: Prop := c.Advice 0 1 = c.b
--EXITED REGION: load private
--REGION: load private
--Annotation: private input
def advice_0_2: Prop := c.Advice 0 2 = c.c
--EXITED REGION: load private
--REGION: add
def selector_0_3: Prop := c.Selector 0 3 = 1
--Annotation: lhs
def advice_0_3: Prop := c.Advice 0 3 = c.a
def copy_0: Prop := c.Advice 0 3 = c.Advice 0 0
--Annotation: rhs
def advice_1_3: Prop := c.Advice 1 3 = c.b
def copy_1: Prop := c.Advice 1 3 = c.Advice 0 1
--Annotation: lhs + rhs
def advice_0_4: Prop := c.Advice 0 4 = (c.a) + (c.b)
--EXITED REGION: add
--REGION: mul
def selector_1_5: Prop := c.Selector 1 5 = 1
--Annotation: lhs
def advice_0_5: Prop := c.Advice 0 5 = (c.a) + (c.b)
def copy_2: Prop := c.Advice 0 5 = c.Advice 0 4
--Annotation: rhs
def advice_1_5: Prop := c.Advice 1 5 = c.c
def copy_3: Prop := c.Advice 1 5 = c.Advice 0 2
--Annotation: lhs * rhs
def advice_0_6: Prop := c.Advice 0 6 = ((c.a) + (c.b)) * (c.c)
--EXITED REGION: mul
def copy_4: Prop := c.Advice 0 6 = c.Instance 0 0
------GATES-------
def gate_0: Prop := ∀ row : ℕ,  c.Selector 0 row * (c.Advice  0 (row) + c.Advice  1 (row) - c.Advice  0 (row + 1)) = 0
def gate_1: Prop := ∀ row : ℕ,  c.Selector 1 row * (c.Advice  0 (row) * c.Advice  1 (row) - c.Advice  0 (row + 1)) = 0

def advice_func: ℕ → ℕ → ZMod P :=
      λ x y => match x with
        | 0 => match y with
          | 0 => c.a
          | 1 => c.b
          | 2 => c.c
          | 3 => c.a
          | 4 => (c.a) + (c.b)
          | 5 => (c.a) + (c.b)
          | 6 => ((c.a) + (c.b)) * (c.c)
          | _ => 0
        | 1 => match y with
          | 3 => c.b
          | 5 => c.c
          | _ => 0
        | _ => 0

def all_copy_constraints: Prop :=
  copy_0 c ∧
  copy_1 c ∧
  copy_2 c ∧
  copy_3 c ∧
  copy_4 c

def all_gates: Prop :=
  gate_0 c ∧
  gate_1 c

def selector_0_n: Prop := ∀ row : ℕ, row ≠ 3 → c.Selector 0 row = 0
def selector_1_n: Prop := ∀ row : ℕ, row ≠ 5 → c.Selector 1 row = 0
def all_selectors: Prop :=
  selector_0_3 c ∧
  selector_0_n c ∧
  selector_1_5 c ∧
  selector_1_n c

def meets_constraints: Prop := all_selectors c ∧ all_gates c ∧ all_copy_constraints c

def spec (x y z: ZMod P): Prop := (x + y) * z = c.Instance 0 0
end TwoChip

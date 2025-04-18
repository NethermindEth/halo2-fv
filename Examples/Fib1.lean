import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Fibonacci.Ex1

def S_T_from_P (S T P : ℕ) : Prop :=
  (2^S * T = P - 1) ∧
  (∀ s' t': ℕ, 2^s' * t' = P - 1 → s' ≤ S)
def multiplicative_generator (P: ℕ) (mult_gen: ZMod P) : Prop :=
  mult_gen ^ P = 1
structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  AdviceUnassigned: ℕ → ℕ → ZMod P
  AdvicePhase: ℕ → ℕ
  Fixed: ℕ → ℕ → ZMod P
  FixedUnassigned: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  InstanceUnassigned: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
  Challenges: (ℕ → ℕ → ZMod P) → ℕ → ℕ → ZMod P
  num_blinding_factors: ℕ
  S: ℕ
  T: ℕ
  k: ℕ
  mult_gen: ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P}
def Circuit.isValid (c: Circuit P P_Prime) : Prop :=
  S_T_from_P c.S c.T P ∧
  multiplicative_generator P c.mult_gen ∧ (
  ∀ advice1 advice2: ℕ → ℕ → ZMod P, ∀ phase: ℕ,
    (∀ row col, (col < 3 ∧ c.AdvicePhase col ≤ phase) → advice1 col row = advice2 col row) →
    (∀ i, c.Challenges advice1 i phase = c.Challenges advice2 i phase)
  )
abbrev ValidCircuit (P: ℕ) (P_Prime: Nat.Prime P) : Type := {c: Circuit P P_Prime // c.isValid}
namespace ValidCircuit
def get_advice (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Advice col row
def get_fixed (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Fixed col row
def get_instance (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Instance col row
def get_selector (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => c.1.Selector col row
def get_challenge (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ idx phase => c.1.Challenges c.1.Advice idx phase
def k (c: ValidCircuit P P_Prime) := c.1.k
def n (c: ValidCircuit P P_Prime) := 2^c.k
def usable_rows (c: ValidCircuit P P_Prime) := c.n - (c.1.num_blinding_factors + 1)
def S (c: ValidCircuit P P_Prime) := c.1.S
def T (c: ValidCircuit P P_Prime) := c.1.T
def mult_gen (c: ValidCircuit P P_Prime) := c.1.mult_gen
def root_of_unity (c: ValidCircuit P P_Prime) : ZMod P := c.mult_gen ^ c.T
def delta (c: ValidCircuit P P_Prime) : ZMod P := c.mult_gen ^ (2^c.S)
end ValidCircuit
def is_shuffle (c: ValidCircuit P P_Prime) (shuffle: ℕ → ℕ): Prop :=
  ∃ inv: ℕ → ℕ,
  ∀ row: ℕ,
    inv (shuffle row) = row ∧
    (row ≥ c.usable_rows → shuffle row = row)
def sufficient_rows (c: ValidCircuit P P_Prime) : Prop :=
  c.n ≥ 8 --cs.minimum_rows
--End preamble
def assertions (c: ValidCircuit P P_Prime): Prop :=
  true

-- Entered region: first row
  ∧ 0 < c.usable_rows -- Selector 0 enabled
  ∧ 0 < c.usable_rows -- Instance 0 query
  ∧ 0 < c.usable_rows -- Advice 0 assignment
  ∧ 0 < c.usable_rows ∧ 0 < c.usable_rows -- Copy 0 to 0 assignment
  ∧ 1 < c.usable_rows -- Instance 0 query
  ∧ 0 < c.usable_rows -- Advice 1 assignment
  ∧ 0 < c.usable_rows ∧ 1 < c.usable_rows -- Copy 1 to 0 assignment
  ∧ 0 < c.usable_rows -- Advice 2 assignment
-- Exited region: first row

-- Entered region: next row
  ∧ 1 < c.usable_rows -- Selector 0 enabled
  ∧ 1 < c.usable_rows -- Advice 0 assignment
  ∧ 1 < c.usable_rows ∧ 0 < c.usable_rows -- Copy 0 to 1 assignment
  ∧ 1 < c.usable_rows -- Advice 1 assignment
  ∧ 1 < c.usable_rows ∧ 0 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 1 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row

-- Entered region: next row
  ∧ 2 < c.usable_rows -- Selector 0 enabled
  ∧ 2 < c.usable_rows -- Advice 0 assignment
  ∧ 2 < c.usable_rows ∧ 0 < c.usable_rows -- Copy 0 to 2 assignment
  ∧ 2 < c.usable_rows -- Advice 1 assignment
  ∧ 2 < c.usable_rows ∧ 1 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 2 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row

-- Entered region: next row
  ∧ 3 < c.usable_rows -- Selector 0 enabled
  ∧ 3 < c.usable_rows -- Advice 0 assignment
  ∧ 3 < c.usable_rows ∧ 1 < c.usable_rows -- Copy 0 to 2 assignment
  ∧ 3 < c.usable_rows -- Advice 1 assignment
  ∧ 3 < c.usable_rows ∧ 2 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 3 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row

-- Entered region: next row
  ∧ 4 < c.usable_rows -- Selector 0 enabled
  ∧ 4 < c.usable_rows -- Advice 0 assignment
  ∧ 4 < c.usable_rows ∧ 2 < c.usable_rows -- Copy 0 to 2 assignment
  ∧ 4 < c.usable_rows -- Advice 1 assignment
  ∧ 4 < c.usable_rows ∧ 3 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 4 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row

-- Entered region: next row
  ∧ 5 < c.usable_rows -- Selector 0 enabled
  ∧ 5 < c.usable_rows -- Advice 0 assignment
  ∧ 5 < c.usable_rows ∧ 3 < c.usable_rows -- Copy 0 to 2 assignment
  ∧ 5 < c.usable_rows -- Advice 1 assignment
  ∧ 5 < c.usable_rows ∧ 4 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 5 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row

-- Entered region: next row
  ∧ 6 < c.usable_rows -- Selector 0 enabled
  ∧ 6 < c.usable_rows -- Advice 0 assignment
  ∧ 6 < c.usable_rows ∧ 4 < c.usable_rows -- Copy 0 to 2 assignment
  ∧ 6 < c.usable_rows -- Advice 1 assignment
  ∧ 6 < c.usable_rows ∧ 5 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 6 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row

-- Entered region: next row
  ∧ 7 < c.usable_rows -- Selector 0 enabled
  ∧ 7 < c.usable_rows -- Advice 0 assignment
  ∧ 7 < c.usable_rows ∧ 5 < c.usable_rows -- Copy 0 to 2 assignment
  ∧ 7 < c.usable_rows -- Advice 1 assignment
  ∧ 7 < c.usable_rows ∧ 6 < c.usable_rows -- Copy 1 to 2 assignment
  ∧ 7 < c.usable_rows -- Advice 2 assignment
-- Exited region: next row
  ∧ 7 < c.usable_rows ∧ 2 < c.usable_rows -- Copy 2 to 0 assignment


def copy_0 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 0 = c.get_instance 0 0
def copy_1 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 0 = c.get_instance 0 1
def copy_2 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 1 = c.get_advice 1 0
def copy_3 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 1 = c.get_advice 2 0
def copy_4 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 2 = c.get_advice 2 0
def copy_5 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 2 = c.get_advice 2 1
def copy_6 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 3 = c.get_advice 2 1
def copy_7 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 3 = c.get_advice 2 2
def copy_8 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 4 = c.get_advice 2 2
def copy_9 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 4 = c.get_advice 2 3
def copy_10 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 5 = c.get_advice 2 3
def copy_11 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 5 = c.get_advice 2 4
def copy_12 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 6 = c.get_advice 2 4
def copy_13 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 6 = c.get_advice 2 5
def copy_14 (c: ValidCircuit P P_Prime): Prop := c.get_advice 0 7 = c.get_advice 2 5
def copy_15 (c: ValidCircuit P P_Prime): Prop := c.get_advice 1 7 = c.get_advice 2 6
def copy_16 (c: ValidCircuit P P_Prime): Prop := c.get_advice 2 7 = c.get_instance 0 2
def copy_0_to_9 (c: ValidCircuit P P_Prime) : Prop :=
  copy_0 c ∧ copy_1 c ∧ copy_2 c ∧ copy_3 c ∧ copy_4 c ∧ copy_5 c ∧ copy_6 c ∧ copy_7 c ∧ copy_8 c ∧ copy_9 c
def copy_10_to_16 (c: ValidCircuit P P_Prime) : Prop :=
  copy_10 c ∧ copy_11 c ∧ copy_12 c ∧ copy_13 c ∧ copy_14 c ∧ copy_15 c ∧ copy_16 c
def all_copy_constraints (c: ValidCircuit P P_Prime): Prop :=
  copy_0_to_9 c ∧ copy_10_to_16 c
def selector_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 8 then 1
  else 0
def selector_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 c row
    | _ => 0
def fixed_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | _ => c.1.FixedUnassigned col row
def advice_phase (c: ValidCircuit P P_Prime) : ℕ → ℕ :=
  λ col => match col with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => 0
def gate_0_0_ (c: ValidCircuit P P_Prime) (row: ℕ) : Prop := 
  (c.get_selector 0 row) * (((c.get_advice 0 row) + (c.get_advice 1 row)) + (-(c.get_advice 2 row))) = 0
def all_gates (c: ValidCircuit P P_Prime): Prop := ∀ row: ℕ,
    gate_0_0_ c row
def all_lookups (c: ValidCircuit P P_Prime): Prop := true
def all_shuffles (c: ValidCircuit P P_Prime) : Prop := true
def meets_constraints (c: ValidCircuit P P_Prime): Prop :=
  sufficient_rows c ∧
  c.1.num_blinding_factors = 5 ∧
  c.1.Selector = selector_func c ∧
  c.1.Fixed = fixed_func c ∧
  c.1.AdvicePhase = advice_phase c ∧
  assertions c  ∧
  all_gates c ∧
  all_copy_constraints c ∧
  all_lookups c ∧
  all_shuffles c ∧
  ∀ col row: ℕ, (row < c.n ∧ row ≥ c.usable_rows) → c.1.Instance col row = c.1.InstanceUnassigned col row
end Fibonacci.Ex1

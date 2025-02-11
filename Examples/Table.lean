import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace LookupExamples.Table

inductive Value (P: ℕ) where
  | Real (x: ZMod P)
  | Poison
inductive CellValue (P: ℕ) where
  | Assigned (x: ZMod P)
  | Unassigned
  | Poison (row: ℕ)
inductive InstanceValue (P: ℕ) where
  | Assigned (x: ZMod P)
  | Padding
def S_T_from_P (S T P : ℕ) : Prop :=
  (2^S * T = P - 1) ∧
  (∀ s' t': ℕ, 2^s' * t' = P - 1 → s' ≤ S)
def multiplicative_generator (P: ℕ) (mult_gen: ZMod P) : Prop :=
  mult_gen ^ P = 1
structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → CellValue P
  AdvicePhase: ℕ → ℕ
  Fixed: ℕ → ℕ → CellValue P
  Instance: ℕ → ℕ → InstanceValue P
  Selector: ℕ → ℕ → ZMod P
  Challenges: (ℕ → ℕ → CellValue P) → ℕ → ℕ → ZMod P
  num_blinding_factors: ℕ
  S: ℕ
  T: ℕ
  k: ℕ
  mult_gen: ZMod P
  sym_value: ZMod P
  sym_lookup_value: ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P}
def eval_cell (cell : CellValue P) : Value P :=
  match cell with
  | .Assigned (x : ZMod P) => .Real x
  | .Unassigned            => .Real 0
  | .Poison (_ : ℕ)      => .Poison

def instance_to_field (cell : InstanceValue P) : ZMod P :=
  match cell with
  | .Assigned x => x
  | .Padding    => 0

def eval_instance (inst : InstanceValue P) : Value P :=
  .Real (instance_to_field inst)

def cell_of_inst (inst : InstanceValue P) : CellValue P :=
  .Assigned (instance_to_field inst)

instance {P : ℕ} : Coe (InstanceValue P) (CellValue P) where
  coe := cell_of_inst

instance : Neg (Value P) := ⟨λ x ↦
  match x with
  | .Real x => .Real (-x)
  | .Poison => .Poison
⟩

instance : Add (Value P) := ⟨λ x y ↦
  match x, y with
  | .Real x₁, .Real x₂ => .Real (x₁ + x₂)
  | .Poison, .Poison   => .Poison
  | .Poison, .Real _   => .Poison
  | .Real _, .Poison   => .Poison
⟩

-- Should this handle (x - x)?
instance : Sub (Value P) := ⟨λ x y ↦ x + (-y)⟩

instance : Mul (Value P) := ⟨λ x y ↦
  match x, y with
  | .Real x₁, .Real x₂ => .Real (x₁ * x₂)
  | .Poison, .Poison   => .Poison
  | .Poison, .Real x₁  => if x₁ = 0 then .Real 0 else .Poison
  | .Real x₁, .Poison  => if x₁ = 0 then .Real 0 else .Poison
⟩
def Circuit.isValid (c: Circuit P P_Prime) : Prop :=
  S_T_from_P c.S c.T P ∧
  multiplicative_generator P c.mult_gen ∧ (
  ∀ advice1 advice2: ℕ → ℕ → CellValue P, ∀ phase: ℕ,
    (∀ row col, (col < 1 ∧ c.AdvicePhase col ≤ phase) → advice1 col row = advice2 col row) →
    (∀ i, c.Challenges advice1 i phase = c.Challenges advice2 i phase)
  )
abbrev ValidCircuit (P: ℕ) (P_Prime: Nat.Prime P) : Type := {c: Circuit P P_Prime // c.isValid}
namespace ValidCircuit
def get_advice (c: ValidCircuit P P_Prime) : ℕ → ℕ → Value P :=
  λ col row => eval_cell (c.1.Advice col row)
def get_fixed (c: ValidCircuit P P_Prime) : ℕ → ℕ → Value P :=
  λ col row => eval_cell (c.1.Fixed col row)
def get_instance (c: ValidCircuit P P_Prime) : ℕ → ℕ → Value P :=
  λ col row => eval_instance (c.1.Instance col row)
def get_selector (c: ValidCircuit P P_Prime) : ℕ → ℕ → Value P :=
  λ col row => .Real (c.1.Selector col row)
def get_challenge (c: ValidCircuit P P_Prime) : ℕ → ℕ → Value P :=
  λ idx phase => .Real (c.1.Challenges c.1.Advice idx phase)
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

-- Entered region: load range-check table
  ∧ 0 < c.usable_rows -- Fixed 0 assignment
  ∧ 1 < c.usable_rows -- Fixed 0 assignment
  ∧ 2 < c.usable_rows -- Fixed 0 assignment
  ∧ 3 < c.usable_rows -- Fixed 0 assignment
  ∧ 4 < c.usable_rows -- Fixed 0 assignment
  ∧ 5 < c.usable_rows -- Fixed 0 assignment
  ∧ 6 < c.usable_rows -- Fixed 0 assignment
  ∧ 7 < c.usable_rows -- Fixed 0 assignment
  ∧ 8 < c.usable_rows -- Fixed 0 assignment
  ∧ 9 < c.usable_rows -- Fixed 0 assignment
  ∧ 10 < c.usable_rows -- Fixed 0 assignment
  ∧ 11 < c.usable_rows -- Fixed 0 assignment
  ∧ 12 < c.usable_rows -- Fixed 0 assignment
  ∧ 13 < c.usable_rows -- Fixed 0 assignment
  ∧ 14 < c.usable_rows -- Fixed 0 assignment
  ∧ 15 < c.usable_rows -- Fixed 0 assignment
  ∧ 16 < c.usable_rows -- Fixed 0 assignment
  ∧ 17 < c.usable_rows -- Fixed 0 assignment
  ∧ 18 < c.usable_rows -- Fixed 0 assignment
  ∧ 19 < c.usable_rows -- Fixed 0 assignment
  ∧ 20 < c.usable_rows -- Fixed 0 assignment
  ∧ 21 < c.usable_rows -- Fixed 0 assignment
  ∧ 22 < c.usable_rows -- Fixed 0 assignment
  ∧ 23 < c.usable_rows -- Fixed 0 assignment
  ∧ 24 < c.usable_rows -- Fixed 0 assignment
  ∧ 25 < c.usable_rows -- Fixed 0 assignment
  ∧ 26 < c.usable_rows -- Fixed 0 assignment
  ∧ 27 < c.usable_rows -- Fixed 0 assignment
  ∧ 28 < c.usable_rows -- Fixed 0 assignment
  ∧ 29 < c.usable_rows -- Fixed 0 assignment
  ∧ 0 < c.usable_rows -- Fixed 1 assignment
  ∧ 1 < c.usable_rows -- Fixed 1 assignment
  ∧ 2 < c.usable_rows -- Fixed 1 assignment
  ∧ 3 < c.usable_rows -- Fixed 1 assignment
  ∧ 4 < c.usable_rows -- Fixed 1 assignment
  ∧ 5 < c.usable_rows -- Fixed 1 assignment
  ∧ 6 < c.usable_rows -- Fixed 1 assignment
  ∧ 7 < c.usable_rows -- Fixed 1 assignment
  ∧ 8 < c.usable_rows -- Fixed 1 assignment
  ∧ 9 < c.usable_rows -- Fixed 1 assignment
  ∧ 10 < c.usable_rows -- Fixed 1 assignment
  ∧ 11 < c.usable_rows -- Fixed 1 assignment
  ∧ 12 < c.usable_rows -- Fixed 1 assignment
  ∧ 13 < c.usable_rows -- Fixed 1 assignment
  ∧ 14 < c.usable_rows -- Fixed 1 assignment
  ∧ 15 < c.usable_rows -- Fixed 1 assignment
  ∧ 16 < c.usable_rows -- Fixed 1 assignment
  ∧ 17 < c.usable_rows -- Fixed 1 assignment
  ∧ 18 < c.usable_rows -- Fixed 1 assignment
  ∧ 19 < c.usable_rows -- Fixed 1 assignment
  ∧ 20 < c.usable_rows -- Fixed 1 assignment
  ∧ 21 < c.usable_rows -- Fixed 1 assignment
  ∧ 22 < c.usable_rows -- Fixed 1 assignment
  ∧ 23 < c.usable_rows -- Fixed 1 assignment
  ∧ 24 < c.usable_rows -- Fixed 1 assignment
  ∧ 25 < c.usable_rows -- Fixed 1 assignment
  ∧ 26 < c.usable_rows -- Fixed 1 assignment
  ∧ 27 < c.usable_rows -- Fixed 1 assignment
  ∧ 28 < c.usable_rows -- Fixed 1 assignment
  ∧ 29 < c.usable_rows -- Fixed 1 assignment
-- Exited region: load range-check table
 ∧ 30 < c.usable_rows -- Fixed 0 fill from row
 ∧ 30 < c.usable_rows -- Fixed 1 fill from row

-- Entered region: Assign value for simple range check
  ∧ 0 < c.usable_rows -- Selector 0 enabled
  ∧ 0 < c.usable_rows -- Advice 0 assignment
-- Exited region: Assign value for simple range check

-- Entered region: Assign value for lookup range check
  ∧ 1 < c.usable_rows -- Selector 1 enabled
  ∧ 1 < c.usable_rows -- Advice 0 assignment
-- Exited region: Assign value for lookup range check


def all_copy_constraints (_c: ValidCircuit P P_Prime): Prop := true
def selector_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 1 then 1
  else 0
def selector_func_col_1 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 1 then 0
  else if row < 2 then 1
  else 0
def selector_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 c row
    | 1 => selector_func_col_1 c row
    | _ => 0
def fixed_func_col_0_0_to_9 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 0 then .Assigned 3
  else if row = 1 then .Assigned 4
  else if row = 2 then .Assigned 5
  else if row = 3 then .Assigned 6
  else if row = 4 then .Assigned 7
  else if row = 5 then .Assigned 8
  else if row = 6 then .Assigned 9
  else if row = 7 then .Assigned 10
  else if row = 8 then .Assigned 11
  else if row = 9 then .Assigned 12
  else .Unassigned
def fixed_func_col_0_10_to_19 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 10 then .Assigned 13
  else if row = 11 then .Assigned 14
  else if row = 12 then .Assigned 15
  else if row = 13 then .Assigned 16
  else if row = 14 then .Assigned 17
  else if row = 15 then .Assigned 18
  else if row = 16 then .Assigned 19
  else if row = 17 then .Assigned 20
  else if row = 18 then .Assigned 21
  else if row = 19 then .Assigned 22
  else .Unassigned
def fixed_func_col_0_20_to_29 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 20 then .Assigned 23
  else if row = 21 then .Assigned 24
  else if row = 22 then .Assigned 25
  else if row = 23 then .Assigned 26
  else if row = 24 then .Assigned 27
  else if row = 25 then .Assigned 28
  else if row = 26 then .Assigned 29
  else if row = 27 then .Assigned 30
  else if row = 28 then .Assigned 31
  else if row = 29 then .Assigned 32
  else .Unassigned
def fixed_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row ≥ 30 then .Assigned 3
  else if row ≤ 9 then fixed_func_col_0_0_to_9 c row
  else if row ≤ 19 then fixed_func_col_0_10_to_19 c row
  else if row ≤ 29 then fixed_func_col_0_20_to_29 c row
  else .Unassigned
def fixed_func_col_1_0_to_9 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 0 then .Assigned 0
  else if row = 1 then .Assigned 1
  else if row = 2 then .Assigned 2
  else if row = 3 then .Assigned 3
  else if row = 4 then .Assigned 4
  else if row = 5 then .Assigned 5
  else if row = 6 then .Assigned 6
  else if row = 7 then .Assigned 7
  else if row = 8 then .Assigned 8
  else if row = 9 then .Assigned 9
  else .Unassigned
def fixed_func_col_1_10_to_19 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 10 then .Assigned 10
  else if row = 11 then .Assigned 11
  else if row = 12 then .Assigned 12
  else if row = 13 then .Assigned 13
  else if row = 14 then .Assigned 14
  else if row = 15 then .Assigned 15
  else if row = 16 then .Assigned 16
  else if row = 17 then .Assigned 17
  else if row = 18 then .Assigned 18
  else if row = 19 then .Assigned 19
  else .Unassigned
def fixed_func_col_1_20_to_29 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 20 then .Assigned 20
  else if row = 21 then .Assigned 21
  else if row = 22 then .Assigned 22
  else if row = 23 then .Assigned 23
  else if row = 24 then .Assigned 24
  else if row = 25 then .Assigned 25
  else if row = 26 then .Assigned 26
  else if row = 27 then .Assigned 27
  else if row = 28 then .Assigned 28
  else if row = 29 then .Assigned 29
  else .Unassigned
def fixed_func_col_1 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row ≥ 30 then .Assigned 0
  else if row ≤ 9 then fixed_func_col_1_0_to_9 c row
  else if row ≤ 19 then fixed_func_col_1_10_to_19 c row
  else if row ≤ 29 then fixed_func_col_1_20_to_29 c row
  else .Unassigned
def fixed_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → CellValue P :=
  λ col row => match col with
    | 0 => fixed_func_col_0 c row
    | 1 => fixed_func_col_1 c row
    | _ => .Unassigned
def advice_phase (c: ValidCircuit P P_Prime) : ℕ → ℕ :=
  λ col => match col with
  | 0 => 0
  | _ => 0
def gate_0_0_range_check (c: ValidCircuit P P_Prime) (row: ℕ) : Prop := 
  (c.get_selector 0 row) * ((((((((c.get_advice 0 row) * (((.Real 1)) + (-(c.get_advice 0 row)))) * (((.Real 2)) + (-(c.get_advice 0 row)))) * (((.Real 3)) + (-(c.get_advice 0 row)))) * (((.Real 4)) + (-(c.get_advice 0 row)))) * (((.Real 5)) + (-(c.get_advice 0 row)))) * (((.Real 6)) + (-(c.get_advice 0 row)))) * (((.Real 7)) + (-(c.get_advice 0 row)))) = Value.Real 0
def all_gates (c: ValidCircuit P P_Prime): Prop := ∀ row: ℕ,
    gate_0_0_range_check c row
--Lookup argument: table look
def lookup_table_look (c: ValidCircuit P P_Prime) : Prop := ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ ((c.get_selector 1 row) * (c.get_advice 0 row)) = (c.get_fixed 0 lookup_row)
def all_lookups (c: ValidCircuit P P_Prime): Prop := lookup_table_look c
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
  ∀ col row: ℕ, (row < c.n ∧ row ≥ c.usable_rows) → c.1.Instance col row = .Padding
end LookupExamples.Table

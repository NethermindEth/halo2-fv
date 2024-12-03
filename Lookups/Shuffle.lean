import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace ShuffleExample

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
  Fixed: ℕ → ℕ → CellValue P
  Instance: ℕ → ℕ → InstanceValue P
  Selector: ℕ → ℕ → ZMod P
  Challenges: ℕ → ℕ → ZMod P
  num_blinding_factors: ℕ
  S: ℕ
  T: ℕ
  k: ℕ
  mult_gen: ZMod P
  sym_a1: ZMod P
  sym_a2: ZMod P
  sym_a3: ZMod P
  sym_a4: ZMod P
  sym_b1: ZMod P
  sym_b2: ZMod P
  sym_b3: ZMod P
  sym_b4: ZMod P
  sym_c1: ZMod P
  sym_c2: ZMod P
  sym_c3: ZMod P
  sym_c4: ZMod P
  sym_d1: ZMod P
  sym_d2: ZMod P
  sym_d3: ZMod P
  sym_d4: ZMod P
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
  multiplicative_generator P c.mult_gen
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
  λ idx phase => .Real (c.1.Challenges idx phase)
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
--End preamble
def sufficient_rows (c: ValidCircuit P P_Prime) : Prop :=
  c.n ≥ 8 --cs.minimum_rows
def assertions (c: ValidCircuit P P_Prime): Prop :=
  true

-- Entered region: load inputs
  ∧ 0 < c.usable_rows -- Advice 0 assignment
  ∧ 0 < c.usable_rows -- Fixed 0 assignment
  ∧ 0 < c.usable_rows -- Selector 1 enabled
  ∧ 1 < c.usable_rows -- Advice 0 assignment
  ∧ 1 < c.usable_rows -- Fixed 0 assignment
  ∧ 1 < c.usable_rows -- Selector 1 enabled
  ∧ 2 < c.usable_rows -- Advice 0 assignment
  ∧ 2 < c.usable_rows -- Fixed 0 assignment
  ∧ 2 < c.usable_rows -- Selector 1 enabled
  ∧ 3 < c.usable_rows -- Advice 0 assignment
  ∧ 3 < c.usable_rows -- Fixed 0 assignment
  ∧ 3 < c.usable_rows -- Selector 1 enabled
-- Exited region: load inputs

-- Entered region: load shuffles
  ∧ 0 < c.usable_rows -- Advice 1 assignment
  ∧ 0 < c.usable_rows -- Advice 2 assignment
  ∧ 0 < c.usable_rows -- Selector 0 enabled
  ∧ 1 < c.usable_rows -- Advice 1 assignment
  ∧ 1 < c.usable_rows -- Advice 2 assignment
  ∧ 1 < c.usable_rows -- Selector 0 enabled
  ∧ 2 < c.usable_rows -- Advice 1 assignment
  ∧ 2 < c.usable_rows -- Advice 2 assignment
  ∧ 2 < c.usable_rows -- Selector 0 enabled
  ∧ 3 < c.usable_rows -- Advice 1 assignment
  ∧ 3 < c.usable_rows -- Advice 2 assignment
  ∧ 3 < c.usable_rows -- Selector 0 enabled
-- Exited region: load shuffles


def all_copy_constraints (_c: ValidCircuit P P_Prime): Prop := true
def selector_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 4 then 1
  else 0
def selector_func_col_1 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 4 then 1
  else 0
def selector_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 c row
    | 1 => selector_func_col_1 c row
    | _ => 0
def fixed_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → CellValue P :=
  λ row =>
  if row = 0 then .Assigned c.1.sym_b1
  else if row = 1 then .Assigned c.1.sym_b2
  else if row = 2 then .Assigned c.1.sym_b3
  else if row = 3 then .Assigned c.1.sym_b4
  else .Unassigned
def fixed_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → CellValue P :=
  λ col row => match col with
    | 0 => fixed_func_col_0 c row
    | _ => .Unassigned
def all_gates (c: ValidCircuit P P_Prime): Prop := ∀ row: ℕ,
  true
def all_lookups (c: ValidCircuit P P_Prime): Prop := true
def shuffle_shuffle (c: ValidCircuit P P_Prime): Prop := ∃ shuffle, is_shuffle c shuffle ∧ (∀ row : ℕ, row < c.usable_rows → ((c.get_selector 1 row) * (c.get_advice 0 row), (c.get_selector 1 row) * (c.get_fixed 0 row)) = ((c.get_selector 0 (shuffle row)) * (c.get_advice 1 (shuffle row)), (c.get_selector 0 (shuffle row)) * (c.get_advice 2 (shuffle row))))
def all_shuffles (c: ValidCircuit P P_Prime) : Prop := shuffle_shuffle c
def meets_constraints (c: ValidCircuit P P_Prime): Prop :=
  sufficient_rows c ∧
  c.1.num_blinding_factors = 5 ∧
  c.1.Selector = selector_func c ∧
  c.1.Fixed = fixed_func c ∧
  assertions c  ∧
  all_gates c ∧
  all_copy_constraints c ∧
  all_lookups c ∧
  all_shuffles c ∧
  ∀ col row: ℕ, (row < c.n ∧ row ≥ c.usable_rows) → c.1.Instance col row = .Padding
end ShuffleExample

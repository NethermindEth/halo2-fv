import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Fibonacci.Ex2

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

-- Entered region: entire fibonacci table
  ∧ 0 < c.usable_rows -- Selector 0 enabled
  ∧ 1 < c.usable_rows -- Selector 0 enabled
  ∧ 0 < c.usable_rows -- Instance 0 query
  ∧ 0 < c.usable_rows -- Advice 0 assignment
  ∧ 0 < c.usable_rows ∧ 0 < c.usable_rows -- Copy 0 to 0 assignment
  ∧ 1 < c.usable_rows -- Instance 0 query
  ∧ 1 < c.usable_rows -- Advice 0 assignment
  ∧ 1 < c.usable_rows ∧ 1 < c.usable_rows -- Copy 0 to 0 assignment
  ∧ 2 < c.usable_rows -- Selector 0 enabled
  ∧ 2 < c.usable_rows -- Advice 0 assignment
  ∧ 3 < c.usable_rows -- Selector 0 enabled
  ∧ 3 < c.usable_rows -- Advice 0 assignment
  ∧ 4 < c.usable_rows -- Selector 0 enabled
  ∧ 4 < c.usable_rows -- Advice 0 assignment
  ∧ 5 < c.usable_rows -- Selector 0 enabled
  ∧ 5 < c.usable_rows -- Advice 0 assignment
  ∧ 6 < c.usable_rows -- Selector 0 enabled
  ∧ 6 < c.usable_rows -- Advice 0 assignment
  ∧ 7 < c.usable_rows -- Selector 0 enabled
  ∧ 7 < c.usable_rows -- Advice 0 assignment
  ∧ 8 < c.usable_rows -- Advice 0 assignment
  ∧ 9 < c.usable_rows -- Advice 0 assignment
-- Exited region: entire fibonacci table
  ∧ 9 < c.usable_rows ∧ 2 < c.usable_rows -- Copy 0 to 0 assignment


def copy_0 (c: ValidCircuit P P_Prime): Prop := c.1.Advice 0 0 = ↑(c.1.Instance 0 0)
def copy_1 (c: ValidCircuit P P_Prime): Prop := c.1.Advice 0 1 = ↑(c.1.Instance 0 1)
def copy_2 (c: ValidCircuit P P_Prime): Prop := c.1.Advice 0 9 = ↑(c.1.Instance 0 2)
def all_copy_constraints (c: ValidCircuit P P_Prime): Prop :=
  copy_0 c ∧ copy_1 c ∧ copy_2 c
def selector_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 8 then 1
  else 0
def selector_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 c row
    | _ => 0
def fixed_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → CellValue P :=
  λ col _ => match col with
    | _ => .Unassigned
def gate_0_0_ (c: ValidCircuit P P_Prime) (row: ℕ) : Prop := 
  (c.get_selector 0 row) * (((c.get_advice 0 row) + (c.get_advice 0 ((row + 1) % c.n))) + (-(c.get_advice 0 ((row + 2) % c.n)))) = Value.Real 0
def all_gates (c: ValidCircuit P P_Prime): Prop := ∀ row: ℕ,
    gate_0_0_ c row
def all_lookups (c: ValidCircuit P P_Prime): Prop := true
def all_shuffles (c: ValidCircuit P P_Prime) : Prop := true
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
end Fibonacci.Ex2

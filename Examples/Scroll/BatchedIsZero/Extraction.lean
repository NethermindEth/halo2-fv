import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

set_option linter.unusedVariables false

namespace BatchedIsZero

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
    (∀ row col, (col < 6 ∧ c.AdvicePhase col ≤ phase) → advice1 col row = advice2 col row) →
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

-- Entered region: witness
-- Exited region: witness


def all_copy_constraints (c: ValidCircuit P P_Prime): Prop :=
  true
def selector_func_col_0 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
  λ row =>
  if row < 1 then 1
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
  | _ => 0
  -- Advice column annotations:
-- Advice Column 0
  -- 0: value
-- Advice Column 1
  -- 0: value
-- Advice Column 2
  -- 0: value
-- Advice Column 3
  -- 0: expect_is_zero
-- Advice Column 4
  -- 0: is_zero
-- Advice Column 5
  -- 0: nonempty_witness
  -- Instance column annotations:
  -- None
def gate_0 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1 name: "is_zero is bool" part 1/1 
  ∀ row: ℕ, ((c.get_selector 0 row) * (c.get_advice 4 row)) * ((c.get_advice 4 row) + (-((1)))) = 0
def gate_1 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 2 name: "is_zero is 0 if there is any non-zero value" part 1/3 
  ∀ row: ℕ, ((c.get_selector 0 row) * (c.get_advice 4 row)) * (c.get_advice 0 row) = 0
def gate_2 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 2 name: "is_zero is 0 if there is any non-zero value" part 2/3 
  ∀ row: ℕ, ((c.get_selector 0 row) * (c.get_advice 4 row)) * (c.get_advice 1 row) = 0
def gate_3 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 2 name: "is_zero is 0 if there is any non-zero value" part 3/3 
  ∀ row: ℕ, ((c.get_selector 0 row) * (c.get_advice 4 row)) * (c.get_advice 2 row) = 0
def gate_4 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 3 name: "is_zero is 1 if values are all zero" part 1/1 
  ∀ row: ℕ, (c.get_selector 0 row) * ((((((1)) + (-(c.get_advice 4 row))) * (((1)) + (-((c.get_advice 0 row) * (c.get_advice 5 row))))) * (((1)) + (-((c.get_advice 1 row) * (c.get_advice 5 row))))) * (((1)) + (-((c.get_advice 2 row) * (c.get_advice 5 row))))) = 0
def gate_5 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 4 name: "check is_zero" part 1/1 
  ∀ row: ℕ, (c.get_selector 0 row) * ((c.get_advice 4 row) + (-(c.get_advice 3 row))) = 0
def all_gates (c: ValidCircuit P P_Prime): Prop :=
  gate_0 c ∧ gate_1 c ∧ gate_2 c ∧ gate_3 c ∧ gate_4 c ∧ gate_5 c
def all_lookups (c: ValidCircuit P P_Prime): Prop :=
  true
def all_shuffles (c: ValidCircuit P P_Prime) : Prop := true
def meets_constraints (c: ValidCircuit P P_Prime): Prop :=
  sufficient_rows c ∧
  c.1.num_blinding_factors = 5 ∧
  c.1.Selector = selector_func c ∧
  c.1.Fixed = fixed_func c ∧
  c.1.AdvicePhase = advice_phase c ∧
  c.usable_rows ≥ 1 ∧
  all_gates c ∧
  all_copy_constraints c ∧
  all_lookups c ∧
  all_shuffles c ∧
  ∀ col row: ℕ, (row < c.n ∧ row ≥ c.usable_rows) → c.1.Instance col row = c.1.InstanceUnassigned col row
end BatchedIsZero

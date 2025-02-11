import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace ShuffleExample

def S_T_from_P (S T P : ℕ) : Prop :=
  (2^S * T = P - 1) ∧
  (∀ s' t': ℕ, 2^s' * t' = P - 1 → s' ≤ S)

def multiplicative_generator (P: ℕ) (mult_gen: ZMod P) : Prop :=
  mult_gen ^ P = 1

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
  S: ℕ
  T: ℕ
  k: ℕ
  mult_gen: ZMod P

variable {P: ℕ} {P_Prime: Nat.Prime P}

def Circuit.isValid (c: Circuit P P_Prime) : Prop :=
  S_T_from_P c.S c.T P ∧
  multiplicative_generator P c.mult_gen


abbrev ValidCircuit (P: ℕ) (P_Prime: Nat.Prime P) : Type := {c: Circuit P P_Prime // c.isValid}
variable (c: ValidCircuit P P_Prime)

namespace ValidCircuit
def Advice := c.1.Advice
def Fixed := c.1.Fixed
def Instance := c.1.Instance
def Selector := c.1.Selector
def k := c.1.k
def S := c.1.S
def T := c.1.T
def mult_gen := c.1.mult_gen
def root_of_unity : ZMod P :=
  c.mult_gen ^ c.T
def delta : ZMod P :=
  c.mult_gen ^ (2^c.S)
end ValidCircuit

def is_shuffle (shuffle: ℕ → ℕ): Prop :=
  ∃ inv: ℕ → ℕ,
  ∀ row: ℕ,
    inv (shuffle row) = row ∧
    (row ≥ (2^c.k) → shuffle row = row)

-- Entered region: load inputs
-- Exited region: load inputs

-- Entered region: load shuffles
-- Exited region: load shuffles
def all_copy_constraints (_c: ValidCircuit P P_Prime): Prop := true
def selector_func_col_0 : ℕ → ZMod P :=
  λ row =>
    if row > 3 then 0
    else if row > 1 then 2
    else 1


def selector_func_col_1 : ℕ → ZMod P :=
  λ row =>
    if row > 999 then 0
    else 1
def selector_func : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 row
    | 1 => selector_func_col_1 row
    | _ => 0

set_option maxRecDepth 0
def fixed_func_col_0 : ℕ → ZMod P :=
  λ row =>
-- No submap for 0
    -- if row ∈ (Finset.sort (· ≤ ·) {0, 3, 0, 3}) then ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + (100)
    -- else if row = 1 then ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + (20)
    -- else if row = 2 then ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * ((2) * (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) + (40)
    -- else 0
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
    ite (row = 0) 0 (
      ite (row = 0) 0 (
ite (row = 0) 0 (
      ite (row = 0) 0 (
        ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
     ite (row = 0) 0 (
      ite (row = 0) 0 (
      1
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
    )
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => fixed_func_col_0 row
    | _ => 0
------GATES-------
def all_gates (_c: ValidCircuit P P_Prime): Prop := true
--Shuffles: [Argument { input_expressions: [Product(Selector(Selector(1, false)), Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }), Product(Selector(Selector(1, false)), Fixed { query_index: 0, column_index: 0, rotation: Rotation(0) })], shuffle_expressions: [Product(Selector(Selector(0, false)), Advice { query_index: 1, column_index: 1, rotation: Rotation(0) }), Product(Selector(Selector(0, false)), Advice { query_index: 2, column_index: 2, rotation: Rotation(0) })] }]
def shuffle_shuffle : Prop := ∃ shuffle, is_shuffle c shuffle ∧ (∀ row : ℕ, row < (2^c.k) → ((c.Selector 1 row) * (c.Advice 0 row), (c.Selector 1 row) * (c.Fixed 0 row)) = ((c.Selector 0 (shuffle row)) * (c.Advice 1 (shuffle row)), (c.Selector 0 (shuffle row)) * (c.Advice 2 (shuffle row))))
def all_shuffles : Prop := shuffle_shuffle c
def meets_constraints: Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func ∧ all_shuffles c
end ShuffleExample

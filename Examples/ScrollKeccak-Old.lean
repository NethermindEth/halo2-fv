-- NUM_ROUNDS: 24
-- num_rows_per_round: 12
-- num_rows: 1024
-- 1
-- Some(1)
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Scroll.Keccak

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
    (∀ row col, (col < 94 ∧ c.AdvicePhase col ≤ phase) → advice1 col row = advice2 col row) →
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
  c.n ≥ 61 --cs.minimum_rows
--End preamble
def assertions (c: ValidCircuit P P_Prime): Prop :=
  true


def all_copy_constraints (c: ValidCircuit P P_Prime): Prop :=
  true
def selector_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | _ => 0
def fixed_func (c: ValidCircuit P P_Prime) : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | _ => c.1.FixedUnassigned col row
def advice_phase (c: ValidCircuit P P_Prime) : ℕ → ℕ :=
  λ col => match col with
  | 1 => 1
  | 3 => 1
  | 5 => 1
  | 6 => 2
  | _ => 0
def gate_0 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 1/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((134217728) * ((0))) + (c.get_advice 10 ((row + 5) % c.n)))) + (c.get_advice 10 ((row + 4) % c.n)))) + (c.get_advice 10 ((row + 3) % c.n)))) + (c.get_advice 10 ((row + 2) % c.n)))) + (c.get_advice 10 ((row + 1) % c.n)))) + (c.get_advice 10 row)) + (-((c.get_advice 9 ((row + 1) % c.n)) + (c.get_advice 9 ((row + 2) % c.n))))) = 0
def gate_1 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 2/82 absorb result
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((134217728) * ((0))) + (c.get_advice 11 ((row + 5) % c.n)))) + (c.get_advice 11 ((row + 4) % c.n)))) + (c.get_advice 11 ((row + 3) % c.n)))) + (c.get_advice 11 ((row + 2) % c.n)))) + (c.get_advice 11 ((row + 1) % c.n)))) + (c.get_advice 11 row)) + (-(c.get_advice 9 ((row + 3) % c.n)))) = 0
def gate_2 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 3/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 12 ((row + 7) % c.n)))) + (c.get_advice 12 ((row + 6) % c.n)))) + (c.get_advice 12 ((row + 5) % c.n)))) + (c.get_advice 12 ((row + 4) % c.n)))) + (c.get_advice 12 ((row + 3) % c.n)))) + (c.get_advice 12 ((row + 2) % c.n)))) + (c.get_advice 12 ((row + 1) % c.n)))) + (c.get_advice 12 row)) + (-(c.get_advice 9 ((row + 2) % c.n)))) = 0
def gate_3 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 4/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 15 ((row + 9) % c.n)))) + (c.get_advice 15 ((row + 8) % c.n)))) + (c.get_advice 15 ((row + 7) % c.n)))) + (c.get_advice 15 ((row + 6) % c.n)))) + (c.get_advice 15 ((row + 5) % c.n)))) + (c.get_advice 15 ((row + 4) % c.n)))) + (c.get_advice 15 ((row + 3) % c.n)))) + (c.get_advice 15 ((row + 2) % c.n)))) + (c.get_advice 15 ((row + 1) % c.n)))) + (c.get_advice 15 row)) + (-(((((c.get_advice 7 row) + (c.get_advice 7 ((row + 1) % c.n))) + (c.get_advice 7 ((row + 2) % c.n))) + (c.get_advice 7 ((row + 3) % c.n))) + (c.get_advice 7 ((row + 4) % c.n))))) = 0
def gate_4 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 5/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 16 ((row + 7) % c.n)))) + (c.get_advice 16 ((row + 6) % c.n)))) + (c.get_advice 16 ((row + 5) % c.n)))) + (c.get_advice 16 ((row + 4) % c.n)))) + (c.get_advice 16 ((row + 3) % c.n)))) + (c.get_advice 16 ((row + 2) % c.n)))) + (c.get_advice 16 ((row + 1) % c.n)))) + (c.get_advice 16 row))) + (c.get_advice 15 ((row + 11) % c.n)))) + (c.get_advice 15 ((row + 10) % c.n))) + (-(((((c.get_advice 7 ((row + 5) % c.n)) + (c.get_advice 7 ((row + 6) % c.n))) + (c.get_advice 7 ((row + 7) % c.n))) + (c.get_advice 7 ((row + 8) % c.n))) + (c.get_advice 7 ((row + 9) % c.n))))) = 0
def gate_5 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 6/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 17 ((row + 5) % c.n)))) + (c.get_advice 17 ((row + 4) % c.n)))) + (c.get_advice 17 ((row + 3) % c.n)))) + (c.get_advice 17 ((row + 2) % c.n)))) + (c.get_advice 17 ((row + 1) % c.n)))) + (c.get_advice 17 row))) + (c.get_advice 16 ((row + 11) % c.n)))) + (c.get_advice 16 ((row + 10) % c.n)))) + (c.get_advice 16 ((row + 9) % c.n)))) + (c.get_advice 16 ((row + 8) % c.n))) + (-(((((c.get_advice 7 ((row + 10) % c.n)) + (c.get_advice 7 ((row + 11) % c.n))) + (c.get_advice 8 row)) + (c.get_advice 8 ((row + 1) % c.n))) + (c.get_advice 8 ((row + 2) % c.n))))) = 0
def gate_6 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 7/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 18 ((row + 3) % c.n)))) + (c.get_advice 18 ((row + 2) % c.n)))) + (c.get_advice 18 ((row + 1) % c.n)))) + (c.get_advice 18 row))) + (c.get_advice 17 ((row + 11) % c.n)))) + (c.get_advice 17 ((row + 10) % c.n)))) + (c.get_advice 17 ((row + 9) % c.n)))) + (c.get_advice 17 ((row + 8) % c.n)))) + (c.get_advice 17 ((row + 7) % c.n)))) + (c.get_advice 17 ((row + 6) % c.n))) + (-(((((c.get_advice 8 ((row + 3) % c.n)) + (c.get_advice 8 ((row + 4) % c.n))) + (c.get_advice 8 ((row + 5) % c.n))) + (c.get_advice 8 ((row + 6) % c.n))) + (c.get_advice 8 ((row + 7) % c.n))))) = 0
def gate_7 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 8/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 19 ((row + 1) % c.n)))) + (c.get_advice 19 row))) + (c.get_advice 18 ((row + 11) % c.n)))) + (c.get_advice 18 ((row + 10) % c.n)))) + (c.get_advice 18 ((row + 9) % c.n)))) + (c.get_advice 18 ((row + 8) % c.n)))) + (c.get_advice 18 ((row + 7) % c.n)))) + (c.get_advice 18 ((row + 6) % c.n)))) + (c.get_advice 18 ((row + 5) % c.n)))) + (c.get_advice 18 ((row + 4) % c.n))) + (-(((((c.get_advice 8 ((row + 8) % c.n)) + (c.get_advice 8 ((row + 9) % c.n))) + (c.get_advice 8 ((row + 10) % c.n))) + (c.get_advice 8 ((row + 11) % c.n))) + (c.get_advice 9 row)))) = 0
def gate_8 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 9/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 25 ((row + 7) % c.n)))) + (c.get_advice 25 ((row + 6) % c.n)))) + (c.get_advice 25 ((row + 5) % c.n)))) + (c.get_advice 25 ((row + 4) % c.n)))) + (c.get_advice 25 ((row + 3) % c.n)))) + (c.get_advice 25 ((row + 2) % c.n)))) + (c.get_advice 25 ((row + 1) % c.n)))) + (c.get_advice 25 row)) + (-((c.get_advice 7 row) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 24 ((row + 1) % c.n)))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 7) % c.n))))))) = 0
def gate_9 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 10/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 85 row) + ((8) * (c.get_advice 85 ((row + 1) % c.n)))) + (-(c.get_advice 30 ((row + 4) % c.n)))) = 0
def gate_0_to_9 (c: ValidCircuit P P_Prime) : Prop :=
  gate_0 c ∧ gate_1 c ∧ gate_2 c ∧ gate_3 c ∧ gate_4 c ∧ gate_5 c ∧ gate_6 c ∧ gate_7 c ∧ gate_8 c ∧ gate_9 c
def gate_10 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 11/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((8) * ((0))) + (c.get_advice 85 row))) + (c.get_advice 30 ((row + 11) % c.n)))) + (c.get_advice 30 ((row + 10) % c.n)))) + (c.get_advice 30 ((row + 9) % c.n)))) + (c.get_advice 30 ((row + 8) % c.n)))) + (c.get_advice 30 ((row + 7) % c.n)))) + (c.get_advice 30 ((row + 6) % c.n)))) + (c.get_advice 30 ((row + 5) % c.n)))) + (c.get_advice 85 ((row + 1) % c.n))) + (-((c.get_advice 7 ((row + 5) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 20 ((row + 9) % c.n)))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row)) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 5) % c.n))))))) = 0
def gate_11 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 12/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 85 ((row + 2) % c.n)) + ((262144) * (c.get_advice 85 ((row + 3) % c.n)))) + (-(c.get_advice 40 ((row + 3) % c.n)))) = 0
def gate_12 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 13/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((64) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((262144) * ((0))) + (c.get_advice 85 ((row + 2) % c.n)))) + (c.get_advice 40 ((row + 2) % c.n)))) + (c.get_advice 40 ((row + 1) % c.n)))) + (c.get_advice 40 row))) + (c.get_advice 35 ((row + 11) % c.n)))) + (c.get_advice 35 ((row + 10) % c.n)))) + (c.get_advice 35 ((row + 9) % c.n)))) + (c.get_advice 35 ((row + 8) % c.n)))) + (c.get_advice 85 ((row + 3) % c.n))) + (-((c.get_advice 7 ((row + 10) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 21 ((row + 7) % c.n)))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 3) % c.n))))))) = 0
def gate_13 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 14/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 85 ((row + 4) % c.n)) + ((4096) * (c.get_advice 85 ((row + 5) % c.n)))) + (-(c.get_advice 25 ((row + 11) % c.n)))) = 0
def gate_14 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 15/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((4096) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((4096) * ((0))) + (c.get_advice 85 ((row + 4) % c.n)))) + (c.get_advice 25 ((row + 10) % c.n)))) + (c.get_advice 25 ((row + 9) % c.n)))) + (c.get_advice 25 ((row + 8) % c.n)))) + (c.get_advice 30 ((row + 3) % c.n)))) + (c.get_advice 30 ((row + 2) % c.n)))) + (c.get_advice 30 ((row + 1) % c.n)))) + (c.get_advice 30 row))) + (c.get_advice 85 ((row + 5) % c.n))) + (-((c.get_advice 8 ((row + 3) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 22 ((row + 5) % c.n)))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n)))) + (c.get_advice 24 ((row + 1) % c.n))))))) = 0
def gate_15 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 16/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 85 ((row + 6) % c.n)) + ((512) * (c.get_advice 85 ((row + 7) % c.n)))) + (-(c.get_advice 35 ((row + 3) % c.n)))) = 0
def gate_16 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 17/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((32768) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((512) * ((0))) + (c.get_advice 85 ((row + 6) % c.n)))) + (c.get_advice 35 ((row + 2) % c.n)))) + (c.get_advice 35 ((row + 1) % c.n)))) + (c.get_advice 35 row))) + (c.get_advice 35 ((row + 7) % c.n)))) + (c.get_advice 35 ((row + 6) % c.n)))) + (c.get_advice 35 ((row + 5) % c.n)))) + (c.get_advice 35 ((row + 4) % c.n)))) + (c.get_advice 85 ((row + 7) % c.n))) + (-((c.get_advice 8 ((row + 8) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 23 ((row + 3) % c.n)))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row))) + (c.get_advice 20 ((row + 9) % c.n))))))) = 0
def gate_17 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 18/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 85 ((row + 8) % c.n)) + ((4096) * (c.get_advice 85 ((row + 9) % c.n)))) + (-(c.get_advice 36 ((row + 4) % c.n)))) = 0
def gate_18 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 19/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((4096) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((4096) * ((0))) + (c.get_advice 85 ((row + 8) % c.n)))) + (c.get_advice 36 ((row + 3) % c.n)))) + (c.get_advice 36 ((row + 2) % c.n)))) + (c.get_advice 36 ((row + 1) % c.n)))) + (c.get_advice 36 row))) + (c.get_advice 36 ((row + 7) % c.n)))) + (c.get_advice 36 ((row + 6) % c.n)))) + (c.get_advice 36 ((row + 5) % c.n)))) + (c.get_advice 85 ((row + 9) % c.n))) + (-((c.get_advice 7 ((row + 1) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 24 ((row + 1) % c.n)))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 7) % c.n))))))) = 0
def gate_19 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 20/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 85 ((row + 10) % c.n)) + ((4096) * (c.get_advice 85 ((row + 11) % c.n)))) + (-(c.get_advice 26 ((row + 5) % c.n)))) = 0
def gate_10_to_19 (c: ValidCircuit P P_Prime) : Prop :=
  gate_10 c ∧ gate_11 c ∧ gate_12 c ∧ gate_13 c ∧ gate_14 c ∧ gate_15 c ∧ gate_16 c ∧ gate_17 c ∧ gate_18 c ∧ gate_19 c
def gate_20 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 21/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((4096) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((4096) * ((0))) + (c.get_advice 85 ((row + 10) % c.n)))) + (c.get_advice 26 ((row + 4) % c.n)))) + (c.get_advice 26 ((row + 3) % c.n)))) + (c.get_advice 26 ((row + 2) % c.n)))) + (c.get_advice 26 ((row + 1) % c.n)))) + (c.get_advice 26 row))) + (c.get_advice 26 ((row + 7) % c.n)))) + (c.get_advice 26 ((row + 6) % c.n)))) + (c.get_advice 85 ((row + 11) % c.n))) + (-((c.get_advice 7 ((row + 6) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 20 ((row + 9) % c.n)))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row)) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 5) % c.n))))))) = 0
def gate_21 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 22/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 86 row) + ((262144) * (c.get_advice 86 ((row + 1) % c.n)))) + (-(c.get_advice 31 ((row + 4) % c.n)))) = 0
def gate_22 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 23/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((64) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((262144) * ((0))) + (c.get_advice 86 row))) + (c.get_advice 31 ((row + 11) % c.n)))) + (c.get_advice 31 ((row + 10) % c.n)))) + (c.get_advice 31 ((row + 9) % c.n)))) + (c.get_advice 31 ((row + 8) % c.n)))) + (c.get_advice 31 ((row + 7) % c.n)))) + (c.get_advice 31 ((row + 6) % c.n)))) + (c.get_advice 31 ((row + 5) % c.n)))) + (c.get_advice 86 ((row + 1) % c.n))) + (-((c.get_advice 7 ((row + 11) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 21 ((row + 7) % c.n)))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 3) % c.n))))))) = 0
def gate_23 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 24/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 86 ((row + 2) % c.n)) + ((2097152) * (c.get_advice 86 ((row + 3) % c.n)))) + (-(c.get_advice 41 ((row + 2) % c.n)))) = 0
def gate_24 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 25/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((2097152) * ((0))) + (c.get_advice 86 ((row + 2) % c.n)))) + (c.get_advice 41 ((row + 1) % c.n)))) + (c.get_advice 41 row))) + (c.get_advice 36 ((row + 11) % c.n)))) + (c.get_advice 36 ((row + 10) % c.n)))) + (c.get_advice 36 ((row + 9) % c.n)))) + (c.get_advice 36 ((row + 8) % c.n)))) + (c.get_advice 41 ((row + 3) % c.n)))) + (c.get_advice 86 ((row + 3) % c.n))) + (-((c.get_advice 8 ((row + 4) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 22 ((row + 5) % c.n)))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n)))) + (c.get_advice 24 ((row + 1) % c.n))))))) = 0
def gate_25 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 26/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 86 ((row + 4) % c.n)) + ((4096) * (c.get_advice 86 ((row + 5) % c.n)))) + (-(c.get_advice 26 ((row + 10) % c.n)))) = 0
def gate_26 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 27/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((4096) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((4096) * ((0))) + (c.get_advice 86 ((row + 4) % c.n)))) + (c.get_advice 26 ((row + 9) % c.n)))) + (c.get_advice 26 ((row + 8) % c.n)))) + (c.get_advice 31 ((row + 3) % c.n)))) + (c.get_advice 31 ((row + 2) % c.n)))) + (c.get_advice 31 ((row + 1) % c.n)))) + (c.get_advice 31 row))) + (c.get_advice 26 ((row + 11) % c.n)))) + (c.get_advice 86 ((row + 5) % c.n))) + (-((c.get_advice 8 ((row + 9) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 23 ((row + 3) % c.n)))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row))) + (c.get_advice 20 ((row + 9) % c.n))))))) = 0
def gate_27 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 28/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 86 ((row + 6) % c.n)) + ((512) * (c.get_advice 86 ((row + 7) % c.n)))) + (-(c.get_advice 27 ((row + 8) % c.n)))) = 0
def gate_28 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 29/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((32768) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((512) * ((0))) + (c.get_advice 86 ((row + 6) % c.n)))) + (c.get_advice 32 ((row + 3) % c.n)))) + (c.get_advice 32 ((row + 2) % c.n)))) + (c.get_advice 32 ((row + 1) % c.n)))) + (c.get_advice 32 row))) + (c.get_advice 27 ((row + 11) % c.n)))) + (c.get_advice 27 ((row + 10) % c.n)))) + (c.get_advice 27 ((row + 9) % c.n)))) + (c.get_advice 86 ((row + 7) % c.n))) + (-((c.get_advice 7 ((row + 2) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 24 ((row + 1) % c.n)))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 7) % c.n))))))) = 0
def gate_29 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 30/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 86 ((row + 8) % c.n)) + ((64) * (c.get_advice 86 ((row + 9) % c.n)))) + (-(c.get_advice 37 ((row + 1) % c.n)))) = 0
def gate_20_to_29 (c: ValidCircuit P P_Prime) : Prop :=
  gate_20 c ∧ gate_21 c ∧ gate_22 c ∧ gate_23 c ∧ gate_24 c ∧ gate_25 c ∧ gate_26 c ∧ gate_27 c ∧ gate_28 c ∧ gate_29 c
def gate_30 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 31/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((262144) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((64) * ((0))) + (c.get_advice 86 ((row + 8) % c.n)))) + (c.get_advice 37 row))) + (c.get_advice 37 ((row + 7) % c.n)))) + (c.get_advice 37 ((row + 6) % c.n)))) + (c.get_advice 37 ((row + 5) % c.n)))) + (c.get_advice 37 ((row + 4) % c.n)))) + (c.get_advice 37 ((row + 3) % c.n)))) + (c.get_advice 37 ((row + 2) % c.n)))) + (c.get_advice 86 ((row + 9) % c.n))) + (-((c.get_advice 7 ((row + 7) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 20 ((row + 9) % c.n)))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row)) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 5) % c.n))))))) = 0
def gate_31 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 32/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 86 ((row + 10) % c.n)) + ((512) * (c.get_advice 86 ((row + 11) % c.n)))) + (-(c.get_advice 27 ((row + 5) % c.n)))) = 0
def gate_32 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 33/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((32768) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((512) * ((0))) + (c.get_advice 86 ((row + 10) % c.n)))) + (c.get_advice 27 ((row + 4) % c.n)))) + (c.get_advice 27 ((row + 3) % c.n)))) + (c.get_advice 27 ((row + 2) % c.n)))) + (c.get_advice 27 ((row + 1) % c.n)))) + (c.get_advice 27 row))) + (c.get_advice 27 ((row + 7) % c.n)))) + (c.get_advice 27 ((row + 6) % c.n)))) + (c.get_advice 86 ((row + 11) % c.n))) + (-((c.get_advice 8 row) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 21 ((row + 7) % c.n)))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 3) % c.n))))))) = 0
def gate_33 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 34/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 87 row) + ((8) * (c.get_advice 87 ((row + 1) % c.n)))) + (-(c.get_advice 32 ((row + 7) % c.n)))) = 0
def gate_34 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 35/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((8) * ((0))) + (c.get_advice 87 row))) + (c.get_advice 32 ((row + 6) % c.n)))) + (c.get_advice 32 ((row + 5) % c.n)))) + (c.get_advice 32 ((row + 4) % c.n)))) + (c.get_advice 32 ((row + 11) % c.n)))) + (c.get_advice 32 ((row + 10) % c.n)))) + (c.get_advice 32 ((row + 9) % c.n)))) + (c.get_advice 32 ((row + 8) % c.n)))) + (c.get_advice 87 ((row + 1) % c.n))) + (-((c.get_advice 8 ((row + 5) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 22 ((row + 5) % c.n)))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n)))) + (c.get_advice 24 ((row + 1) % c.n))))))) = 0
def gate_35 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 36/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 87 ((row + 2) % c.n)) + ((2097152) * (c.get_advice 87 ((row + 3) % c.n)))) + (-(c.get_advice 42 row))) = 0
def gate_36 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 37/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((2097152) * ((0))) + (c.get_advice 87 ((row + 2) % c.n)))) + (c.get_advice 37 ((row + 11) % c.n)))) + (c.get_advice 37 ((row + 10) % c.n)))) + (c.get_advice 37 ((row + 9) % c.n)))) + (c.get_advice 37 ((row + 8) % c.n)))) + (c.get_advice 42 ((row + 3) % c.n)))) + (c.get_advice 42 ((row + 2) % c.n)))) + (c.get_advice 42 ((row + 1) % c.n)))) + (c.get_advice 87 ((row + 3) % c.n))) + (-((c.get_advice 8 ((row + 10) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 23 ((row + 3) % c.n)))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row))) + (c.get_advice 20 ((row + 9) % c.n))))))) = 0
def gate_37 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 38/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 87 ((row + 4) % c.n)) + ((8) * (c.get_advice 87 ((row + 5) % c.n)))) + (-(c.get_advice 43 ((row + 1) % c.n)))) = 0
def gate_38 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 39/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((2097152) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((8) * ((0))) + (c.get_advice 87 ((row + 4) % c.n)))) + (c.get_advice 43 row))) + (c.get_advice 38 ((row + 11) % c.n)))) + (c.get_advice 38 ((row + 10) % c.n)))) + (c.get_advice 38 ((row + 9) % c.n)))) + (c.get_advice 38 ((row + 8) % c.n)))) + (c.get_advice 43 ((row + 3) % c.n)))) + (c.get_advice 43 ((row + 2) % c.n)))) + (c.get_advice 87 ((row + 5) % c.n))) + (-((c.get_advice 7 ((row + 3) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 24 ((row + 1) % c.n)))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 7) % c.n))))))) = 0
def gate_39 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 40/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 87 ((row + 6) % c.n)) + ((32768) * (c.get_advice 87 ((row + 7) % c.n)))) + (-(c.get_advice 33 ((row + 1) % c.n)))) = 0
def gate_30_to_39 (c: ValidCircuit P P_Prime) : Prop :=
  gate_30 c ∧ gate_31 c ∧ gate_32 c ∧ gate_33 c ∧ gate_34 c ∧ gate_35 c ∧ gate_36 c ∧ gate_37 c ∧ gate_38 c ∧ gate_39 c
def gate_40 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 41/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((512) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((32768) * ((0))) + (c.get_advice 87 ((row + 6) % c.n)))) + (c.get_advice 33 row))) + (c.get_advice 28 ((row + 11) % c.n)))) + (c.get_advice 28 ((row + 10) % c.n)))) + (c.get_advice 28 ((row + 9) % c.n)))) + (c.get_advice 28 ((row + 8) % c.n)))) + (c.get_advice 33 ((row + 3) % c.n)))) + (c.get_advice 33 ((row + 2) % c.n)))) + (c.get_advice 87 ((row + 7) % c.n))) + (-((c.get_advice 7 ((row + 8) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 20 ((row + 9) % c.n)))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row)) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 5) % c.n))))))) = 0
def gate_41 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 42/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 87 ((row + 8) % c.n)) + ((2097152) * (c.get_advice 87 ((row + 9) % c.n)))) + (-(c.get_advice 38 ((row + 1) % c.n)))) = 0
def gate_42 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 43/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((2097152) * ((0))) + (c.get_advice 87 ((row + 8) % c.n)))) + (c.get_advice 38 row))) + (c.get_advice 38 ((row + 7) % c.n)))) + (c.get_advice 38 ((row + 6) % c.n)))) + (c.get_advice 38 ((row + 5) % c.n)))) + (c.get_advice 38 ((row + 4) % c.n)))) + (c.get_advice 38 ((row + 3) % c.n)))) + (c.get_advice 38 ((row + 2) % c.n)))) + (c.get_advice 87 ((row + 9) % c.n))) + (-((c.get_advice 8 ((row + 1) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 21 ((row + 7) % c.n)))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 3) % c.n))))))) = 0
def gate_43 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 44/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 87 ((row + 10) % c.n)) + ((32768) * (c.get_advice 87 ((row + 11) % c.n)))) + (-(c.get_advice 28 ((row + 2) % c.n)))) = 0
def gate_44 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 45/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((512) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((32768) * ((0))) + (c.get_advice 87 ((row + 10) % c.n)))) + (c.get_advice 28 ((row + 1) % c.n)))) + (c.get_advice 28 row))) + (c.get_advice 28 ((row + 7) % c.n)))) + (c.get_advice 28 ((row + 6) % c.n)))) + (c.get_advice 28 ((row + 5) % c.n)))) + (c.get_advice 28 ((row + 4) % c.n)))) + (c.get_advice 28 ((row + 3) % c.n)))) + (c.get_advice 87 ((row + 11) % c.n))) + (-((c.get_advice 8 ((row + 6) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 22 ((row + 5) % c.n)))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n)))) + (c.get_advice 24 ((row + 1) % c.n))))))) = 0
def gate_45 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 46/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 33 ((row + 4) % c.n)))) + (c.get_advice 33 ((row + 11) % c.n)))) + (c.get_advice 33 ((row + 10) % c.n)))) + (c.get_advice 33 ((row + 9) % c.n)))) + (c.get_advice 33 ((row + 8) % c.n)))) + (c.get_advice 33 ((row + 7) % c.n)))) + (c.get_advice 33 ((row + 6) % c.n)))) + (c.get_advice 33 ((row + 5) % c.n))) + (-((c.get_advice 8 ((row + 11) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 23 ((row + 3) % c.n)))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row))) + (c.get_advice 20 ((row + 9) % c.n))))))) = 0
def gate_46 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 47/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 88 row) + ((64) * (c.get_advice 88 ((row + 1) % c.n)))) + (-(c.get_advice 34 ((row + 6) % c.n)))) = 0
def gate_47 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 48/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((262144) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((64) * ((0))) + (c.get_advice 88 row))) + (c.get_advice 34 ((row + 5) % c.n)))) + (c.get_advice 34 ((row + 4) % c.n)))) + (c.get_advice 34 ((row + 11) % c.n)))) + (c.get_advice 34 ((row + 10) % c.n)))) + (c.get_advice 34 ((row + 9) % c.n)))) + (c.get_advice 34 ((row + 8) % c.n)))) + (c.get_advice 34 ((row + 7) % c.n)))) + (c.get_advice 88 ((row + 1) % c.n))) + (-((c.get_advice 7 ((row + 4) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 24 ((row + 1) % c.n)))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 7) % c.n))))))) = 0
def gate_48 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 49/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 88 ((row + 2) % c.n)) + ((64) * (c.get_advice 88 ((row + 3) % c.n)))) + (-(c.get_advice 39 ((row + 8) % c.n)))) = 0
def gate_49 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 50/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((262144) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((64) * ((0))) + (c.get_advice 88 ((row + 2) % c.n)))) + (c.get_advice 44 ((row + 3) % c.n)))) + (c.get_advice 44 ((row + 2) % c.n)))) + (c.get_advice 44 ((row + 1) % c.n)))) + (c.get_advice 44 row))) + (c.get_advice 39 ((row + 11) % c.n)))) + (c.get_advice 39 ((row + 10) % c.n)))) + (c.get_advice 39 ((row + 9) % c.n)))) + (c.get_advice 88 ((row + 3) % c.n))) + (-((c.get_advice 7 ((row + 9) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 20 ((row + 9) % c.n)))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row)) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 5) % c.n))))))) = 0
def gate_40_to_49 (c: ValidCircuit P P_Prime) : Prop :=
  gate_40 c ∧ gate_41 c ∧ gate_42 c ∧ gate_43 c ∧ gate_44 c ∧ gate_45 c ∧ gate_46 c ∧ gate_47 c ∧ gate_48 c ∧ gate_49 c
def gate_50 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 51/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 88 ((row + 4) % c.n)) + ((32768) * (c.get_advice 88 ((row + 5) % c.n)))) + (-(c.get_advice 34 ((row + 3) % c.n)))) = 0
def gate_51 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 52/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((512) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((32768) * ((0))) + (c.get_advice 88 ((row + 4) % c.n)))) + (c.get_advice 34 ((row + 2) % c.n)))) + (c.get_advice 34 ((row + 1) % c.n)))) + (c.get_advice 34 row))) + (c.get_advice 29 ((row + 11) % c.n)))) + (c.get_advice 29 ((row + 10) % c.n)))) + (c.get_advice 29 ((row + 9) % c.n)))) + (c.get_advice 29 ((row + 8) % c.n)))) + (c.get_advice 88 ((row + 5) % c.n))) + (-((c.get_advice 8 ((row + 2) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 21 ((row + 7) % c.n)))) + (c.get_advice 21 ((row + 6) % c.n)))) + (c.get_advice 21 ((row + 5) % c.n)))) + (c.get_advice 21 ((row + 4) % c.n)))) + (c.get_advice 21 ((row + 3) % c.n)))) + (c.get_advice 21 ((row + 2) % c.n)))) + (c.get_advice 21 ((row + 1) % c.n)))) + (c.get_advice 21 row))) + (c.get_advice 20 ((row + 11) % c.n)))) + (c.get_advice 20 ((row + 10) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 3) % c.n))))))) = 0
def gate_52 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 53/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 39 ((row + 6) % c.n)))) + (c.get_advice 39 ((row + 5) % c.n)))) + (c.get_advice 39 ((row + 4) % c.n)))) + (c.get_advice 39 ((row + 3) % c.n)))) + (c.get_advice 39 ((row + 2) % c.n)))) + (c.get_advice 39 ((row + 1) % c.n)))) + (c.get_advice 39 row))) + (c.get_advice 39 ((row + 7) % c.n))) + (-((c.get_advice 8 ((row + 7) % c.n)) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 22 ((row + 5) % c.n)))) + (c.get_advice 22 ((row + 4) % c.n)))) + (c.get_advice 22 ((row + 3) % c.n)))) + (c.get_advice 22 ((row + 2) % c.n)))) + (c.get_advice 22 ((row + 1) % c.n)))) + (c.get_advice 22 row))) + (c.get_advice 21 ((row + 11) % c.n)))) + (c.get_advice 21 ((row + 10) % c.n)))) + (c.get_advice 21 ((row + 9) % c.n)))) + (c.get_advice 21 ((row + 8) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 24 row))) + (c.get_advice 23 ((row + 11) % c.n)))) + (c.get_advice 23 ((row + 10) % c.n)))) + (c.get_advice 23 ((row + 9) % c.n)))) + (c.get_advice 23 ((row + 8) % c.n)))) + (c.get_advice 23 ((row + 7) % c.n)))) + (c.get_advice 23 ((row + 6) % c.n)))) + (c.get_advice 23 ((row + 5) % c.n)))) + (c.get_advice 23 ((row + 4) % c.n)))) + (c.get_advice 24 ((row + 1) % c.n))))))) = 0
def gate_53 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 54/82 rot part
  ∀ row: ℕ, (c.get_fixed 2 row) * (((c.get_advice 88 ((row + 6) % c.n)) + ((262144) * (c.get_advice 88 ((row + 7) % c.n)))) + (-(c.get_advice 29 ((row + 1) % c.n)))) = 0
def gate_54 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 55/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((64) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((262144) * ((0))) + (c.get_advice 88 ((row + 6) % c.n)))) + (c.get_advice 29 row))) + (c.get_advice 29 ((row + 7) % c.n)))) + (c.get_advice 29 ((row + 6) % c.n)))) + (c.get_advice 29 ((row + 5) % c.n)))) + (c.get_advice 29 ((row + 4) % c.n)))) + (c.get_advice 29 ((row + 3) % c.n)))) + (c.get_advice 29 ((row + 2) % c.n)))) + (c.get_advice 88 ((row + 7) % c.n))) + (-((c.get_advice 9 row) + ((((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((8) * ((0))) + (c.get_advice 23 ((row + 3) % c.n)))) + (c.get_advice 23 ((row + 2) % c.n)))) + (c.get_advice 23 ((row + 1) % c.n)))) + (c.get_advice 23 row))) + (c.get_advice 22 ((row + 11) % c.n)))) + (c.get_advice 22 ((row + 10) % c.n)))) + (c.get_advice 22 ((row + 9) % c.n)))) + (c.get_advice 22 ((row + 8) % c.n)))) + (c.get_advice 22 ((row + 7) % c.n)))) + (c.get_advice 22 ((row + 6) % c.n))) + (((8) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * (((2097152) * ((0))) + (c.get_advice 20 ((row + 8) % c.n)))) + (c.get_advice 20 ((row + 7) % c.n)))) + (c.get_advice 20 ((row + 6) % c.n)))) + (c.get_advice 20 ((row + 5) % c.n)))) + (c.get_advice 20 ((row + 4) % c.n)))) + (c.get_advice 20 ((row + 3) % c.n)))) + (c.get_advice 20 ((row + 2) % c.n)))) + (c.get_advice 20 ((row + 1) % c.n)))) + (c.get_advice 20 row))) + (c.get_advice 20 ((row + 9) % c.n))))))) = 0
def gate_55 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 56/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((134217728) * ((0))) + (c.get_advice 89 ((row + 5) % c.n)))) + (c.get_advice 89 ((row + 4) % c.n)))) + (c.get_advice 89 ((row + 3) % c.n)))) + (c.get_advice 89 ((row + 2) % c.n)))) + (c.get_advice 89 ((row + 1) % c.n)))) + (c.get_advice 89 row)) + (-((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 65 ((row + 7) % c.n)))) + (c.get_advice 65 ((row + 6) % c.n)))) + (c.get_advice 65 ((row + 5) % c.n)))) + (c.get_advice 65 ((row + 4) % c.n)))) + (c.get_advice 65 ((row + 3) % c.n)))) + (c.get_advice 65 ((row + 2) % c.n)))) + (c.get_advice 65 ((row + 1) % c.n)))) + (c.get_advice 65 row)) + (c.get_fixed 7 row)))) = 0
def gate_56 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 57/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((8589934592) * (((134217728) * ((0))) + (c.get_advice 90 ((row + 5) % c.n)))) + (c.get_advice 90 ((row + 4) % c.n)))) + (c.get_advice 90 ((row + 3) % c.n)))) + (c.get_advice 90 ((row + 2) % c.n)))) + (c.get_advice 90 ((row + 1) % c.n)))) + (c.get_advice 90 row)) + (-(c.get_advice 7 ((row + 12) % c.n)))) = 0
def gate_57 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 58/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 70 ((row + 3) % c.n)))) + (c.get_advice 70 ((row + 2) % c.n)))) + (c.get_advice 70 ((row + 1) % c.n)))) + (c.get_advice 70 row))) + (c.get_advice 65 ((row + 11) % c.n)))) + (c.get_advice 65 ((row + 10) % c.n)))) + (c.get_advice 65 ((row + 9) % c.n)))) + (c.get_advice 65 ((row + 8) % c.n))) + (-(c.get_advice 7 ((row + 13) % c.n)))) = 0
def gate_58 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 59/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 70 ((row + 11) % c.n)))) + (c.get_advice 70 ((row + 10) % c.n)))) + (c.get_advice 70 ((row + 9) % c.n)))) + (c.get_advice 70 ((row + 8) % c.n)))) + (c.get_advice 70 ((row + 7) % c.n)))) + (c.get_advice 70 ((row + 6) % c.n)))) + (c.get_advice 70 ((row + 5) % c.n)))) + (c.get_advice 70 ((row + 4) % c.n))) + (-(c.get_advice 7 ((row + 14) % c.n)))) = 0
def gate_59 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 60/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 75 ((row + 7) % c.n)))) + (c.get_advice 75 ((row + 6) % c.n)))) + (c.get_advice 75 ((row + 5) % c.n)))) + (c.get_advice 75 ((row + 4) % c.n)))) + (c.get_advice 75 ((row + 3) % c.n)))) + (c.get_advice 75 ((row + 2) % c.n)))) + (c.get_advice 75 ((row + 1) % c.n)))) + (c.get_advice 75 row)) + (-(c.get_advice 7 ((row + 15) % c.n)))) = 0
def gate_50_to_59 (c: ValidCircuit P P_Prime) : Prop :=
  gate_50 c ∧ gate_51 c ∧ gate_52 c ∧ gate_53 c ∧ gate_54 c ∧ gate_55 c ∧ gate_56 c ∧ gate_57 c ∧ gate_58 c ∧ gate_59 c
def gate_60 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 61/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 80 ((row + 3) % c.n)))) + (c.get_advice 80 ((row + 2) % c.n)))) + (c.get_advice 80 ((row + 1) % c.n)))) + (c.get_advice 80 row))) + (c.get_advice 75 ((row + 11) % c.n)))) + (c.get_advice 75 ((row + 10) % c.n)))) + (c.get_advice 75 ((row + 9) % c.n)))) + (c.get_advice 75 ((row + 8) % c.n))) + (-(c.get_advice 7 ((row + 16) % c.n)))) = 0
def gate_61 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 62/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 66 ((row + 7) % c.n)))) + (c.get_advice 66 ((row + 6) % c.n)))) + (c.get_advice 66 ((row + 5) % c.n)))) + (c.get_advice 66 ((row + 4) % c.n)))) + (c.get_advice 66 ((row + 3) % c.n)))) + (c.get_advice 66 ((row + 2) % c.n)))) + (c.get_advice 66 ((row + 1) % c.n)))) + (c.get_advice 66 row)) + (-(c.get_advice 7 ((row + 17) % c.n)))) = 0
def gate_62 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 63/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 71 ((row + 3) % c.n)))) + (c.get_advice 71 ((row + 2) % c.n)))) + (c.get_advice 71 ((row + 1) % c.n)))) + (c.get_advice 71 row))) + (c.get_advice 66 ((row + 11) % c.n)))) + (c.get_advice 66 ((row + 10) % c.n)))) + (c.get_advice 66 ((row + 9) % c.n)))) + (c.get_advice 66 ((row + 8) % c.n))) + (-(c.get_advice 7 ((row + 18) % c.n)))) = 0
def gate_63 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 64/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 71 ((row + 11) % c.n)))) + (c.get_advice 71 ((row + 10) % c.n)))) + (c.get_advice 71 ((row + 9) % c.n)))) + (c.get_advice 71 ((row + 8) % c.n)))) + (c.get_advice 71 ((row + 7) % c.n)))) + (c.get_advice 71 ((row + 6) % c.n)))) + (c.get_advice 71 ((row + 5) % c.n)))) + (c.get_advice 71 ((row + 4) % c.n))) + (-(c.get_advice 7 ((row + 19) % c.n)))) = 0
def gate_64 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 65/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 76 ((row + 7) % c.n)))) + (c.get_advice 76 ((row + 6) % c.n)))) + (c.get_advice 76 ((row + 5) % c.n)))) + (c.get_advice 76 ((row + 4) % c.n)))) + (c.get_advice 76 ((row + 3) % c.n)))) + (c.get_advice 76 ((row + 2) % c.n)))) + (c.get_advice 76 ((row + 1) % c.n)))) + (c.get_advice 76 row)) + (-(c.get_advice 7 ((row + 20) % c.n)))) = 0
def gate_65 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 66/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 81 ((row + 3) % c.n)))) + (c.get_advice 81 ((row + 2) % c.n)))) + (c.get_advice 81 ((row + 1) % c.n)))) + (c.get_advice 81 row))) + (c.get_advice 76 ((row + 11) % c.n)))) + (c.get_advice 76 ((row + 10) % c.n)))) + (c.get_advice 76 ((row + 9) % c.n)))) + (c.get_advice 76 ((row + 8) % c.n))) + (-(c.get_advice 7 ((row + 21) % c.n)))) = 0
def gate_66 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 67/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 67 ((row + 7) % c.n)))) + (c.get_advice 67 ((row + 6) % c.n)))) + (c.get_advice 67 ((row + 5) % c.n)))) + (c.get_advice 67 ((row + 4) % c.n)))) + (c.get_advice 67 ((row + 3) % c.n)))) + (c.get_advice 67 ((row + 2) % c.n)))) + (c.get_advice 67 ((row + 1) % c.n)))) + (c.get_advice 67 row)) + (-(c.get_advice 7 ((row + 22) % c.n)))) = 0
def gate_67 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 68/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 72 ((row + 3) % c.n)))) + (c.get_advice 72 ((row + 2) % c.n)))) + (c.get_advice 72 ((row + 1) % c.n)))) + (c.get_advice 72 row))) + (c.get_advice 67 ((row + 11) % c.n)))) + (c.get_advice 67 ((row + 10) % c.n)))) + (c.get_advice 67 ((row + 9) % c.n)))) + (c.get_advice 67 ((row + 8) % c.n))) + (-(c.get_advice 7 ((row + 23) % c.n)))) = 0
def gate_68 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 69/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 72 ((row + 11) % c.n)))) + (c.get_advice 72 ((row + 10) % c.n)))) + (c.get_advice 72 ((row + 9) % c.n)))) + (c.get_advice 72 ((row + 8) % c.n)))) + (c.get_advice 72 ((row + 7) % c.n)))) + (c.get_advice 72 ((row + 6) % c.n)))) + (c.get_advice 72 ((row + 5) % c.n)))) + (c.get_advice 72 ((row + 4) % c.n))) + (-(c.get_advice 8 ((row + 12) % c.n)))) = 0
def gate_69 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 70/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 77 ((row + 7) % c.n)))) + (c.get_advice 77 ((row + 6) % c.n)))) + (c.get_advice 77 ((row + 5) % c.n)))) + (c.get_advice 77 ((row + 4) % c.n)))) + (c.get_advice 77 ((row + 3) % c.n)))) + (c.get_advice 77 ((row + 2) % c.n)))) + (c.get_advice 77 ((row + 1) % c.n)))) + (c.get_advice 77 row)) + (-(c.get_advice 8 ((row + 13) % c.n)))) = 0
def gate_60_to_69 (c: ValidCircuit P P_Prime) : Prop :=
  gate_60 c ∧ gate_61 c ∧ gate_62 c ∧ gate_63 c ∧ gate_64 c ∧ gate_65 c ∧ gate_66 c ∧ gate_67 c ∧ gate_68 c ∧ gate_69 c
def gate_70 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 71/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 82 ((row + 3) % c.n)))) + (c.get_advice 82 ((row + 2) % c.n)))) + (c.get_advice 82 ((row + 1) % c.n)))) + (c.get_advice 82 row))) + (c.get_advice 77 ((row + 11) % c.n)))) + (c.get_advice 77 ((row + 10) % c.n)))) + (c.get_advice 77 ((row + 9) % c.n)))) + (c.get_advice 77 ((row + 8) % c.n))) + (-(c.get_advice 8 ((row + 14) % c.n)))) = 0
def gate_71 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 72/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 68 ((row + 7) % c.n)))) + (c.get_advice 68 ((row + 6) % c.n)))) + (c.get_advice 68 ((row + 5) % c.n)))) + (c.get_advice 68 ((row + 4) % c.n)))) + (c.get_advice 68 ((row + 3) % c.n)))) + (c.get_advice 68 ((row + 2) % c.n)))) + (c.get_advice 68 ((row + 1) % c.n)))) + (c.get_advice 68 row)) + (-(c.get_advice 8 ((row + 15) % c.n)))) = 0
def gate_72 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 73/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 73 ((row + 3) % c.n)))) + (c.get_advice 73 ((row + 2) % c.n)))) + (c.get_advice 73 ((row + 1) % c.n)))) + (c.get_advice 73 row))) + (c.get_advice 68 ((row + 11) % c.n)))) + (c.get_advice 68 ((row + 10) % c.n)))) + (c.get_advice 68 ((row + 9) % c.n)))) + (c.get_advice 68 ((row + 8) % c.n))) + (-(c.get_advice 8 ((row + 16) % c.n)))) = 0
def gate_73 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 74/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 73 ((row + 11) % c.n)))) + (c.get_advice 73 ((row + 10) % c.n)))) + (c.get_advice 73 ((row + 9) % c.n)))) + (c.get_advice 73 ((row + 8) % c.n)))) + (c.get_advice 73 ((row + 7) % c.n)))) + (c.get_advice 73 ((row + 6) % c.n)))) + (c.get_advice 73 ((row + 5) % c.n)))) + (c.get_advice 73 ((row + 4) % c.n))) + (-(c.get_advice 8 ((row + 17) % c.n)))) = 0
def gate_74 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 75/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 78 ((row + 7) % c.n)))) + (c.get_advice 78 ((row + 6) % c.n)))) + (c.get_advice 78 ((row + 5) % c.n)))) + (c.get_advice 78 ((row + 4) % c.n)))) + (c.get_advice 78 ((row + 3) % c.n)))) + (c.get_advice 78 ((row + 2) % c.n)))) + (c.get_advice 78 ((row + 1) % c.n)))) + (c.get_advice 78 row)) + (-(c.get_advice 8 ((row + 18) % c.n)))) = 0
def gate_75 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 76/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 83 ((row + 3) % c.n)))) + (c.get_advice 83 ((row + 2) % c.n)))) + (c.get_advice 83 ((row + 1) % c.n)))) + (c.get_advice 83 row))) + (c.get_advice 78 ((row + 11) % c.n)))) + (c.get_advice 78 ((row + 10) % c.n)))) + (c.get_advice 78 ((row + 9) % c.n)))) + (c.get_advice 78 ((row + 8) % c.n))) + (-(c.get_advice 8 ((row + 19) % c.n)))) = 0
def gate_76 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 77/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 69 ((row + 7) % c.n)))) + (c.get_advice 69 ((row + 6) % c.n)))) + (c.get_advice 69 ((row + 5) % c.n)))) + (c.get_advice 69 ((row + 4) % c.n)))) + (c.get_advice 69 ((row + 3) % c.n)))) + (c.get_advice 69 ((row + 2) % c.n)))) + (c.get_advice 69 ((row + 1) % c.n)))) + (c.get_advice 69 row)) + (-(c.get_advice 8 ((row + 20) % c.n)))) = 0
def gate_77 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 78/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 74 ((row + 3) % c.n)))) + (c.get_advice 74 ((row + 2) % c.n)))) + (c.get_advice 74 ((row + 1) % c.n)))) + (c.get_advice 74 row))) + (c.get_advice 69 ((row + 11) % c.n)))) + (c.get_advice 69 ((row + 10) % c.n)))) + (c.get_advice 69 ((row + 9) % c.n)))) + (c.get_advice 69 ((row + 8) % c.n))) + (-(c.get_advice 8 ((row + 21) % c.n)))) = 0
def gate_78 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 79/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 74 ((row + 11) % c.n)))) + (c.get_advice 74 ((row + 10) % c.n)))) + (c.get_advice 74 ((row + 9) % c.n)))) + (c.get_advice 74 ((row + 8) % c.n)))) + (c.get_advice 74 ((row + 7) % c.n)))) + (c.get_advice 74 ((row + 6) % c.n)))) + (c.get_advice 74 ((row + 5) % c.n)))) + (c.get_advice 74 ((row + 4) % c.n))) + (-(c.get_advice 8 ((row + 22) % c.n)))) = 0
def gate_79 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 80/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 79 ((row + 7) % c.n)))) + (c.get_advice 79 ((row + 6) % c.n)))) + (c.get_advice 79 ((row + 5) % c.n)))) + (c.get_advice 79 ((row + 4) % c.n)))) + (c.get_advice 79 ((row + 3) % c.n)))) + (c.get_advice 79 ((row + 2) % c.n)))) + (c.get_advice 79 ((row + 1) % c.n)))) + (c.get_advice 79 row)) + (-(c.get_advice 8 ((row + 23) % c.n)))) = 0
def gate_70_to_79 (c: ValidCircuit P P_Prime) : Prop :=
  gate_70 c ∧ gate_71 c ∧ gate_72 c ∧ gate_73 c ∧ gate_74 c ∧ gate_75 c ∧ gate_76 c ∧ gate_77 c ∧ gate_78 c ∧ gate_79 c
def gate_80 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 81/82 next row check
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 84 ((row + 3) % c.n)))) + (c.get_advice 84 ((row + 2) % c.n)))) + (c.get_advice 84 ((row + 1) % c.n)))) + (c.get_advice 84 row))) + (c.get_advice 79 ((row + 11) % c.n)))) + (c.get_advice 79 ((row + 10) % c.n)))) + (c.get_advice 79 ((row + 9) % c.n)))) + (c.get_advice 79 ((row + 8) % c.n))) + (-(c.get_advice 9 ((row + 12) % c.n)))) = 0
def gate_81 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1008 name: "round" part 82/82 split
  ∀ row: ℕ, (c.get_fixed 2 row) * ((((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * (((16777216) * ((0))) + (c.get_advice 92 ((row + 7) % c.n)))) + (c.get_advice 92 ((row + 6) % c.n)))) + (c.get_advice 92 ((row + 5) % c.n)))) + (c.get_advice 92 ((row + 4) % c.n)))) + (c.get_advice 92 ((row + 3) % c.n)))) + (c.get_advice 92 ((row + 2) % c.n)))) + (c.get_advice 92 ((row + 1) % c.n)))) + (c.get_advice 92 row)) + (-(c.get_advice 91 row))) = 0
def gate_82 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 1/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 13) % c.n)) + (-(c.get_advice 7 row)))) = 0
def gate_83 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 2/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 15) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 14) % c.n)))) + (-(c.get_advice 7 ((row + 12) % c.n)))) = 0
def gate_84 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 3/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 25) % c.n)) + (-(c.get_advice 7 ((row + 5) % c.n))))) = 0
def gate_85 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 4/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 27) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 26) % c.n)))) + (-(c.get_advice 7 ((row + 17) % c.n)))) = 0
def gate_86 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 5/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 37) % c.n)) + (-(c.get_advice 7 ((row + 10) % c.n))))) = 0
def gate_87 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 6/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 39) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 38) % c.n)))) + (-(c.get_advice 7 ((row + 22) % c.n)))) = 0
def gate_88 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 7/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 49) % c.n)) + (-(c.get_advice 8 ((row + 3) % c.n))))) = 0
def gate_89 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 8/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 51) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 50) % c.n)))) + (-(c.get_advice 8 ((row + 15) % c.n)))) = 0
def gate_80_to_89 (c: ValidCircuit P P_Prime) : Prop :=
  gate_80 c ∧ gate_81 c ∧ gate_82 c ∧ gate_83 c ∧ gate_84 c ∧ gate_85 c ∧ gate_86 c ∧ gate_87 c ∧ gate_88 c ∧ gate_89 c
def gate_90 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 9/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 61) % c.n)) + (-(c.get_advice 8 ((row + 8) % c.n))))) = 0
def gate_91 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 10/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 63) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 62) % c.n)))) + (-(c.get_advice 8 ((row + 20) % c.n)))) = 0
def gate_92 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 11/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 73) % c.n)) + (-(c.get_advice 7 ((row + 1) % c.n))))) = 0
def gate_93 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 12/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 75) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 74) % c.n)))) + (-(c.get_advice 7 ((row + 13) % c.n)))) = 0
def gate_94 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 13/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 85) % c.n)) + (-(c.get_advice 7 ((row + 6) % c.n))))) = 0
def gate_95 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 14/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 87) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 86) % c.n)))) + (-(c.get_advice 7 ((row + 18) % c.n)))) = 0
def gate_96 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 15/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 97) % c.n)) + (-(c.get_advice 7 ((row + 11) % c.n))))) = 0
def gate_97 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 16/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 99) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 98) % c.n)))) + (-(c.get_advice 7 ((row + 23) % c.n)))) = 0
def gate_98 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 17/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 109) % c.n)) + (-(c.get_advice 8 ((row + 4) % c.n))))) = 0
def gate_99 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 18/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 111) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 110) % c.n)))) + (-(c.get_advice 8 ((row + 16) % c.n)))) = 0
def gate_90_to_99 (c: ValidCircuit P P_Prime) : Prop :=
  gate_90 c ∧ gate_91 c ∧ gate_92 c ∧ gate_93 c ∧ gate_94 c ∧ gate_95 c ∧ gate_96 c ∧ gate_97 c ∧ gate_98 c ∧ gate_99 c
def gate_0_to_99 (c: ValidCircuit P P_Prime) : Prop :=
  gate_0_to_9 c ∧ gate_10_to_19 c ∧ gate_20_to_29 c ∧ gate_30_to_39 c ∧ gate_40_to_49 c ∧ gate_50_to_59 c ∧ gate_60_to_69 c ∧ gate_70_to_79 c ∧ gate_80_to_89 c ∧ gate_90_to_99 c
def gate_100 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 19/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 121) % c.n)) + (-(c.get_advice 8 ((row + 9) % c.n))))) = 0
def gate_101 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 20/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 123) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 122) % c.n)))) + (-(c.get_advice 8 ((row + 21) % c.n)))) = 0
def gate_102 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 21/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 133) % c.n)) + (-(c.get_advice 7 ((row + 2) % c.n))))) = 0
def gate_103 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 22/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 135) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 134) % c.n)))) + (-(c.get_advice 7 ((row + 14) % c.n)))) = 0
def gate_104 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 23/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 145) % c.n)) + (-(c.get_advice 7 ((row + 7) % c.n))))) = 0
def gate_105 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 24/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 147) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 146) % c.n)))) + (-(c.get_advice 7 ((row + 19) % c.n)))) = 0
def gate_106 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 25/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 157) % c.n)) + (-(c.get_advice 8 row)))) = 0
def gate_107 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 26/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 159) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 158) % c.n)))) + (-(c.get_advice 8 ((row + 12) % c.n)))) = 0
def gate_108 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 27/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 169) % c.n)) + (-(c.get_advice 8 ((row + 5) % c.n))))) = 0
def gate_109 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 28/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 171) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 170) % c.n)))) + (-(c.get_advice 8 ((row + 17) % c.n)))) = 0
def gate_100_to_109 (c: ValidCircuit P P_Prime) : Prop :=
  gate_100 c ∧ gate_101 c ∧ gate_102 c ∧ gate_103 c ∧ gate_104 c ∧ gate_105 c ∧ gate_106 c ∧ gate_107 c ∧ gate_108 c ∧ gate_109 c
def gate_110 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 29/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 181) % c.n)) + (-(c.get_advice 8 ((row + 10) % c.n))))) = 0
def gate_111 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 30/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 183) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 182) % c.n)))) + (-(c.get_advice 8 ((row + 22) % c.n)))) = 0
def gate_112 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 31/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 193) % c.n)) + (-(c.get_advice 7 ((row + 3) % c.n))))) = 0
def gate_113 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 32/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 195) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 194) % c.n)))) + (-(c.get_advice 7 ((row + 15) % c.n)))) = 0
def gate_114 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 33/42 absorb verify input
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * ((c.get_advice 9 ((row + 205) % c.n)) + (-(c.get_advice 7 ((row + 8) % c.n))))) = 0
def gate_115 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 34/42 absorb result copy
  ∀ row: ℕ, (c.get_fixed 3 row) * ((((((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))) * (c.get_advice 9 ((row + 207) % c.n))) + ((((1)) + (-(((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row)))))) * (c.get_advice 9 ((row + 206) % c.n)))) + (-(c.get_advice 7 ((row + 20) % c.n)))) = 0
def gate_116 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 35/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 8 ((row + 1) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 8 ((row + 13) % c.n)))) = 0
def gate_117 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 36/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 8 ((row + 6) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 8 ((row + 18) % c.n)))) = 0
def gate_118 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 37/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 8 ((row + 11) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 8 ((row + 23) % c.n)))) = 0
def gate_119 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 38/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 7 ((row + 4) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 7 ((row + 16) % c.n)))) = 0
def gate_110_to_119 (c: ValidCircuit P P_Prime) : Prop :=
  gate_110 c ∧ gate_111 c ∧ gate_112 c ∧ gate_113 c ∧ gate_114 c ∧ gate_115 c ∧ gate_116 c ∧ gate_117 c ∧ gate_118 c ∧ gate_119 c
def gate_120 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 39/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 7 ((row + 9) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 7 ((row + 21) % c.n)))) = 0
def gate_121 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 40/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 8 ((row + 2) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 8 ((row + 14) % c.n)))) = 0
def gate_122 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 41/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 8 ((row + 7) % c.n)) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 8 ((row + 19) % c.n)))) = 0
def gate_123 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1009 name: "absorb" part 42/42 absorb state copy
  ∀ row: ℕ, (c.get_fixed 3 row) * (((c.get_advice 9 row) * (((1)) + (-((c.get_fixed 1 row) + (c.get_advice 0 row))))) + (-(c.get_advice 9 ((row + 12) % c.n)))) = 0
def gate_124 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1042 name: "squeeze" part 1/5 squeeze verify packed
  ∀ row: ℕ, (c.get_fixed 4 row) * (((c.get_fixed 1 row) + (c.get_advice 0 row)) * ((c.get_advice 7 row) + (-(c.get_advice 91 ((row + c.n - (12 % c.n)) % c.n))))) = 0
def gate_125 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1042 name: "squeeze" part 2/5 squeeze verify packed
  ∀ row: ℕ, (c.get_fixed 4 row) * (((c.get_fixed 1 row) + (c.get_advice 0 row)) * ((c.get_advice 7 ((row + 5) % c.n)) + (-(c.get_advice 91 ((row + c.n - (24 % c.n)) % c.n))))) = 0
def gate_126 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1042 name: "squeeze" part 3/5 squeeze verify packed
  ∀ row: ℕ, (c.get_fixed 4 row) * (((c.get_fixed 1 row) + (c.get_advice 0 row)) * ((c.get_advice 7 ((row + 10) % c.n)) + (-(c.get_advice 91 ((row + c.n - (36 % c.n)) % c.n))))) = 0
def gate_127 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1042 name: "squeeze" part 4/5 squeeze verify packed
  ∀ row: ℕ, (c.get_fixed 4 row) * (((c.get_fixed 1 row) + (c.get_advice 0 row)) * ((c.get_advice 8 ((row + 3) % c.n)) + (-(c.get_advice 91 ((row + c.n - (48 % c.n)) % c.n))))) = 0
def gate_128 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1042 name: "squeeze" part 5/5 hash rlc check
  ∀ row: ℕ, (c.get_fixed 4 row) * (((c.get_fixed 1 row) + (c.get_advice 0 row)) * (((((((((((((((((((((((((((((((((c.get_advice 93 ((row + c.n - (41 % c.n)) % c.n)) + ((c.get_advice 93 ((row + c.n - (42 % c.n)) % c.n)) * (c.get_challenge 0 0))) + ((c.get_advice 93 ((row + c.n - (43 % c.n)) % c.n)) * ((c.get_challenge 0 0) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (44 % c.n)) % c.n)) * (((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (45 % c.n)) % c.n)) * ((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (46 % c.n)) % c.n)) * (((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (47 % c.n)) % c.n)) * ((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (48 % c.n)) % c.n)) * (((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (29 % c.n)) % c.n)) * ((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (30 % c.n)) % c.n)) * (((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (31 % c.n)) % c.n)) * ((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (32 % c.n)) % c.n)) * (((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (33 % c.n)) % c.n)) * ((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (34 % c.n)) % c.n)) * (((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (35 % c.n)) % c.n)) * ((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (36 % c.n)) % c.n)) * (((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (17 % c.n)) % c.n)) * ((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (18 % c.n)) % c.n)) * (((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (19 % c.n)) % c.n)) * ((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (20 % c.n)) % c.n)) * (((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (21 % c.n)) % c.n)) * ((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (22 % c.n)) % c.n)) * (((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (23 % c.n)) % c.n)) * ((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (24 % c.n)) % c.n)) * (((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (5 % c.n)) % c.n)) * ((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (6 % c.n)) % c.n)) * (((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (7 % c.n)) % c.n)) * ((((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (8 % c.n)) % c.n)) * (((((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (9 % c.n)) % c.n)) * ((((((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (10 % c.n)) % c.n)) * (((((((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (11 % c.n)) % c.n)) * ((((((((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + ((c.get_advice 93 ((row + c.n - (12 % c.n)) % c.n)) * (((((((((((((((((((((((((((((((c.get_challenge 0 0) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)) * (c.get_challenge 0 0)))) + (-(c.get_advice 3 row)))) = 0
def gate_129 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1043 name: "input checks" part 1/1 boolean is_final
  ∀ row: ℕ, (c.get_fixed 0 row) * ((c.get_advice 0 row) * (((1)) + (-(c.get_advice 0 row)))) = 0
def gate_120_to_129 (c: ValidCircuit P P_Prime) : Prop :=
  gate_120 c ∧ gate_121 c ∧ gate_122 c ∧ gate_123 c ∧ gate_124 c ∧ gate_125 c ∧ gate_126 c ∧ gate_127 c ∧ gate_128 c ∧ gate_129 c
def gate_130 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1044 name: "first row" part 1/1 is_final needs to be disabled on the first row
  ∀ row: ℕ, (c.get_fixed 1 row) * (c.get_advice 0 row) = 0
def gate_131 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1046 name: "is final" part 1/2 is_final needs to be the same as the last is_padding in the block
  ∀ row: ℕ, ((1)) * (((c.get_fixed 3 row) + (-(c.get_fixed 1 row))) * ((c.get_advice 0 row) + (-(c.get_advice 14 ((row + c.n - (89 % c.n)) % c.n))))) = 0
def gate_132 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1046 name: "is final" part 2/2 is_final only when q_enable
  ∀ row: ℕ, ((1)) * ((((((((((((((0)) + (c.get_fixed 0 ((row + c.n - (1 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (2 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (3 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (4 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (5 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (6 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (7 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (8 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (9 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (10 % c.n)) % c.n))) + (c.get_fixed 0 ((row + c.n - (11 % c.n)) % c.n))) * (c.get_advice 0 row)) = 0
def gate_133 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 1/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 row) * (((1)) + (-(c.get_advice 14 row))))) = 0
def gate_134 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 2/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 1) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 1) % c.n)))))) = 0
def gate_135 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 3/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 2) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 2) % c.n)))))) = 0
def gate_136 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 4/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 3) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 3) % c.n)))))) = 0
def gate_137 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 5/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 4) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 4) % c.n)))))) = 0
def gate_138 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 6/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 5) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 5) % c.n)))))) = 0
def gate_139 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 7/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 6) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 6) % c.n)))))) = 0
def gate_130_to_139 (c: ValidCircuit P P_Prime) : Prop :=
  gate_130 c ∧ gate_131 c ∧ gate_132 c ∧ gate_133 c ∧ gate_134 c ∧ gate_135 c ∧ gate_136 c ∧ gate_137 c ∧ gate_138 c ∧ gate_139 c
def gate_140 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 8/26 is_padding boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 0 row) * ((c.get_advice 14 ((row + 7) % c.n)) * (((1)) + (-(c.get_advice 14 ((row + 7) % c.n)))))) = 0
def gate_141 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 9/26 last is_padding should be zero on absorb rows
  ∀ row: ℕ, ((1)) * ((c.get_fixed 3 row) * (c.get_advice 14 ((row + 7) % c.n))) = 0
def gate_142 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 10/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 row) + (-(c.get_advice 14 ((row + c.n - (5 % c.n)) % c.n)))) * (((1)) + (-((c.get_advice 14 row) + (-(c.get_advice 14 ((row + c.n - (5 % c.n)) % c.n)))))))) = 0
def gate_143 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 11/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 row)) * ((c.get_advice 13 row) + (-((c.get_advice 14 row) + (-(c.get_advice 14 ((row + c.n - (5 % c.n)) % c.n))))))) = 0
def gate_144 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 12/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 1) % c.n)) + (-(c.get_advice 14 row))) * (((1)) + (-((c.get_advice 14 ((row + 1) % c.n)) + (-(c.get_advice 14 row))))))) = 0
def gate_145 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 13/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 ((row + 1) % c.n))) * ((c.get_advice 13 ((row + 1) % c.n)) + (-((c.get_advice 14 ((row + 1) % c.n)) + (-(c.get_advice 14 row)))))) = 0
def gate_146 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 14/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 2) % c.n)) + (-(c.get_advice 14 ((row + 1) % c.n)))) * (((1)) + (-((c.get_advice 14 ((row + 2) % c.n)) + (-(c.get_advice 14 ((row + 1) % c.n)))))))) = 0
def gate_147 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 15/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 ((row + 2) % c.n))) * ((c.get_advice 13 ((row + 2) % c.n)) + (-((c.get_advice 14 ((row + 2) % c.n)) + (-(c.get_advice 14 ((row + 1) % c.n))))))) = 0
def gate_148 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 16/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 3) % c.n)) + (-(c.get_advice 14 ((row + 2) % c.n)))) * (((1)) + (-((c.get_advice 14 ((row + 3) % c.n)) + (-(c.get_advice 14 ((row + 2) % c.n)))))))) = 0
def gate_149 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 17/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 ((row + 3) % c.n))) * ((c.get_advice 13 ((row + 3) % c.n)) + (-((c.get_advice 14 ((row + 3) % c.n)) + (-(c.get_advice 14 ((row + 2) % c.n))))))) = 0
def gate_140_to_149 (c: ValidCircuit P P_Prime) : Prop :=
  gate_140 c ∧ gate_141 c ∧ gate_142 c ∧ gate_143 c ∧ gate_144 c ∧ gate_145 c ∧ gate_146 c ∧ gate_147 c ∧ gate_148 c ∧ gate_149 c
def gate_150 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 18/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 4) % c.n)) + (-(c.get_advice 14 ((row + 3) % c.n)))) * (((1)) + (-((c.get_advice 14 ((row + 4) % c.n)) + (-(c.get_advice 14 ((row + 3) % c.n)))))))) = 0
def gate_151 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 19/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 ((row + 4) % c.n))) * ((c.get_advice 13 ((row + 4) % c.n)) + (-((c.get_advice 14 ((row + 4) % c.n)) + (-(c.get_advice 14 ((row + 3) % c.n))))))) = 0
def gate_152 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 20/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 5) % c.n)) + (-(c.get_advice 14 ((row + 4) % c.n)))) * (((1)) + (-((c.get_advice 14 ((row + 5) % c.n)) + (-(c.get_advice 14 ((row + 4) % c.n)))))))) = 0
def gate_153 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 21/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 ((row + 5) % c.n))) * ((c.get_advice 13 ((row + 5) % c.n)) + (-((c.get_advice 14 ((row + 5) % c.n)) + (-(c.get_advice 14 ((row + 4) % c.n))))))) = 0
def gate_154 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 22/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 6) % c.n)) + (-(c.get_advice 14 ((row + 5) % c.n)))) * (((1)) + (-((c.get_advice 14 ((row + 6) % c.n)) + (-(c.get_advice 14 ((row + 5) % c.n)))))))) = 0
def gate_155 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 23/26 padding start/intermediate byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 5 row)) * (c.get_advice 14 ((row + 6) % c.n))) * ((c.get_advice 13 ((row + 6) % c.n)) + (-((c.get_advice 14 ((row + 6) % c.n)) + (-(c.get_advice 14 ((row + 5) % c.n))))))) = 0
def gate_156 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 24/26 padding step boolean
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 14 ((row + 7) % c.n)) + (-(c.get_advice 14 ((row + 6) % c.n)))) * (((1)) + (-((c.get_advice 14 ((row + 7) % c.n)) + (-(c.get_advice 14 ((row + 6) % c.n)))))))) = 0
def gate_157 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 25/26 padding start/intermediate byte last byte
  ∀ row: ℕ, ((1)) * (((((1)) * ((c.get_fixed 5 row) + (-(c.get_fixed 6 row)))) * (c.get_advice 14 ((row + 7) % c.n))) * ((c.get_advice 13 ((row + 7) % c.n)) + (-((c.get_advice 14 ((row + 7) % c.n)) + (-(c.get_advice 14 ((row + 6) % c.n))))))) = 0
def gate_158 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1048 name: "padding" part 26/26 padding start/end byte
  ∀ row: ℕ, ((1)) * (((((1)) * (c.get_fixed 6 row)) * (c.get_advice 14 ((row + 7) % c.n))) * ((c.get_advice 13 ((row + 7) % c.n)) + (-(((c.get_advice 14 ((row + 7) % c.n)) + (-(c.get_advice 14 ((row + 6) % c.n)))) + ((128)))))) = 0
def gate_159 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 1/12 update length
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 2 row) + (-(((c.get_advice 2 ((row + c.n - (12 % c.n)) % c.n)) * (((1)) + (-((c.get_fixed 1 ((row + c.n - (12 % c.n)) % c.n)) + (c.get_advice 0 ((row + c.n - (12 % c.n)) % c.n)))))) + ((((((((((0)) + (((1)) + (-(c.get_advice 14 row)))) + (((1)) + (-(c.get_advice 14 ((row + 1) % c.n))))) + (((1)) + (-(c.get_advice 14 ((row + 2) % c.n))))) + (((1)) + (-(c.get_advice 14 ((row + 3) % c.n))))) + (((1)) + (-(c.get_advice 14 ((row + 4) % c.n))))) + (((1)) + (-(c.get_advice 14 ((row + 5) % c.n))))) + (((1)) + (-(c.get_advice 14 ((row + 6) % c.n))))) + (((1)) + (-(c.get_advice 14 ((row + 7) % c.n))))))))) = 0
def gate_150_to_159 (c: ValidCircuit P P_Prime) : Prop :=
  gate_150 c ∧ gate_151 c ∧ gate_152 c ∧ gate_153 c ∧ gate_154 c ∧ gate_155 c ∧ gate_156 c ∧ gate_157 c ∧ gate_158 c ∧ gate_159 c
def gate_160 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 2/12 initial data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * (((c.get_advice 1 ((row + c.n - (12 % c.n)) % c.n)) * (((1)) + (-((c.get_fixed 1 ((row + c.n - (12 % c.n)) % c.n)) + (c.get_advice 0 ((row + c.n - (12 % c.n)) % c.n)))))) + (-(c.get_advice 1 ((row + 8) % c.n))))) = 0
def gate_161 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 3/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 7) % c.n)) + (-(((c.get_advice 14 row) * (c.get_advice 1 ((row + 8) % c.n))) + ((((1)) + (-(c.get_advice 14 row))) * (((c.get_advice 1 ((row + 8) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 row))))))) = 0
def gate_162 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 4/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 6) % c.n)) + (-(((c.get_advice 14 ((row + 1) % c.n)) * (c.get_advice 1 ((row + 7) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 1) % c.n)))) * (((c.get_advice 1 ((row + 7) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 1) % c.n)))))))) = 0
def gate_163 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 5/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 5) % c.n)) + (-(((c.get_advice 14 ((row + 2) % c.n)) * (c.get_advice 1 ((row + 6) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 2) % c.n)))) * (((c.get_advice 1 ((row + 6) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 2) % c.n)))))))) = 0
def gate_164 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 6/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 4) % c.n)) + (-(((c.get_advice 14 ((row + 3) % c.n)) * (c.get_advice 1 ((row + 5) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 3) % c.n)))) * (((c.get_advice 1 ((row + 5) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 3) % c.n)))))))) = 0
def gate_165 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 7/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 3) % c.n)) + (-(((c.get_advice 14 ((row + 4) % c.n)) * (c.get_advice 1 ((row + 4) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 4) % c.n)))) * (((c.get_advice 1 ((row + 4) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 4) % c.n)))))))) = 0
def gate_166 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 8/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 2) % c.n)) + (-(((c.get_advice 14 ((row + 5) % c.n)) * (c.get_advice 1 ((row + 3) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 5) % c.n)))) * (((c.get_advice 1 ((row + 3) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 5) % c.n)))))))) = 0
def gate_167 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 9/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 ((row + 1) % c.n)) + (-(((c.get_advice 14 ((row + 6) % c.n)) * (c.get_advice 1 ((row + 2) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 6) % c.n)))) * (((c.get_advice 1 ((row + 2) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 6) % c.n)))))))) = 0
def gate_168 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 10/12 intermediate data rlc
  ∀ row: ℕ, ((1)) * ((c.get_fixed 5 row) * ((c.get_advice 1 row) + (-(((c.get_advice 14 ((row + 7) % c.n)) * (c.get_advice 1 ((row + 1) % c.n))) + ((((1)) + (-(c.get_advice 14 ((row + 7) % c.n)))) * (((c.get_advice 1 ((row + 1) % c.n)) * (c.get_challenge 1 0)) + (c.get_advice 13 ((row + 7) % c.n)))))))) = 0
def gate_169 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 11/12 length equality check
  ∀ row: ℕ, ((1)) * (((((1)) * ((c.get_fixed 0 row) + (-(c.get_fixed 1 row)))) * (((1)) + (-(c.get_fixed 5 row)))) * ((c.get_advice 2 row) + (-(c.get_advice 2 ((row + c.n - (12 % c.n)) % c.n))))) = 0
def gate_160_to_169 (c: ValidCircuit P P_Prime) : Prop :=
  gate_160 c ∧ gate_161 c ∧ gate_162 c ∧ gate_163 c ∧ gate_164 c ∧ gate_165 c ∧ gate_166 c ∧ gate_167 c ∧ gate_168 c ∧ gate_169 c
def gate_170 (c: ValidCircuit P P_Prime) : Prop :=
  -- Gate number 1049 name: "length and data rlc" part 12/12 data_rlc equality check
  ∀ row: ℕ, ((1)) * (((((1)) * ((c.get_fixed 0 row) + (-(c.get_fixed 1 row)))) * (((1)) + (-(c.get_fixed 5 row)))) * ((c.get_advice 1 row) + (-(c.get_advice 1 ((row + c.n - (12 % c.n)) % c.n))))) = 0
def all_gates (c: ValidCircuit P P_Prime): Prop :=
  gate_0_to_99 c ∧ gate_100_to_109 c ∧ gate_110_to_119 c ∧ gate_120_to_129 c ∧ gate_130_to_139 c ∧ gate_140_to_149 c ∧ gate_150_to_159 c ∧ gate_160_to_169 c ∧ gate_170 c
def lookup_0 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 1 name: "absorb"
  (c.get_advice 10 row, c.get_advice 11 row) = (c.get_fixed 8 lookup_row, c.get_fixed 9 lookup_row)
  
def lookup_1 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 2 name: "input unpack"
  (c.get_advice 12 row, c.get_advice 13 row) = (c.get_fixed 17 lookup_row, c.get_fixed 16 lookup_row)
  
def lookup_2 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 3 name: "theta c"
  (c.get_advice 15 row, c.get_advice 20 row) = (c.get_fixed 12 lookup_row, c.get_fixed 13 lookup_row)
  
def lookup_3 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 4 name: "theta c"
  (c.get_advice 16 row, c.get_advice 21 row) = (c.get_fixed 12 lookup_row, c.get_fixed 13 lookup_row)
  
def lookup_4 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 5 name: "theta c"
  (c.get_advice 17 row, c.get_advice 22 row) = (c.get_fixed 12 lookup_row, c.get_fixed 13 lookup_row)
  
def lookup_5 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 6 name: "theta c"
  (c.get_advice 18 row, c.get_advice 23 row) = (c.get_fixed 12 lookup_row, c.get_fixed 13 lookup_row)
  
def lookup_6 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 7 name: "theta c"
  (c.get_advice 19 row, c.get_advice 24 row) = (c.get_fixed 12 lookup_row, c.get_fixed 13 lookup_row)
  
def lookup_7 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 8 name: "rho/pi"
  (c.get_advice 25 row, c.get_advice 45 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_8 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 9 name: "rho/pi"
  (c.get_advice 40 row, c.get_advice 60 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_9 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 10 name: "rho/pi"
  (c.get_advice 30 row, c.get_advice 50 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_0_to_9 (c: ValidCircuit P P_Prime) : Prop :=
  lookup_0 c ∧ lookup_1 c ∧ lookup_2 c ∧ lookup_3 c ∧ lookup_4 c ∧ lookup_5 c ∧ lookup_6 c ∧ lookup_7 c ∧ lookup_8 c ∧ lookup_9 c
def lookup_10 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 11 name: "rho/pi"
  (c.get_advice 35 row, c.get_advice 55 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_11 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 12 name: "rho/pi"
  (c.get_advice 36 row, c.get_advice 56 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_12 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 13 name: "rho/pi"
  (c.get_advice 26 row, c.get_advice 46 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_13 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 14 name: "rho/pi"
  (c.get_advice 41 row, c.get_advice 61 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_14 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 15 name: "rho/pi"
  (c.get_advice 31 row, c.get_advice 51 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_15 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 16 name: "rho/pi"
  (c.get_advice 32 row, c.get_advice 52 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_16 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 17 name: "rho/pi"
  (c.get_advice 37 row, c.get_advice 57 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_17 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 18 name: "rho/pi"
  (c.get_advice 27 row, c.get_advice 47 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_18 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 19 name: "rho/pi"
  (c.get_advice 42 row, c.get_advice 62 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_19 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 20 name: "rho/pi"
  (c.get_advice 43 row, c.get_advice 63 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_10_to_19 (c: ValidCircuit P P_Prime) : Prop :=
  lookup_10 c ∧ lookup_11 c ∧ lookup_12 c ∧ lookup_13 c ∧ lookup_14 c ∧ lookup_15 c ∧ lookup_16 c ∧ lookup_17 c ∧ lookup_18 c ∧ lookup_19 c
def lookup_20 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 21 name: "rho/pi"
  (c.get_advice 33 row, c.get_advice 53 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_21 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 22 name: "rho/pi"
  (c.get_advice 38 row, c.get_advice 58 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_22 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 23 name: "rho/pi"
  (c.get_advice 28 row, c.get_advice 48 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_23 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 24 name: "rho/pi"
  (c.get_advice 44 row, c.get_advice 64 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_24 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 25 name: "rho/pi"
  (c.get_advice 34 row, c.get_advice 54 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_25 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 26 name: "rho/pi"
  (c.get_advice 39 row, c.get_advice 59 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_26 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 27 name: "rho/pi"
  (c.get_advice 29 row, c.get_advice 49 row) = (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
  
def lookup_27 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 28 name: "pi part range check"
  (c.get_advice 85 row) = (c.get_fixed 10 lookup_row)
  
def lookup_28 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 29 name: "pi part range check"
  (c.get_advice 86 row) = (c.get_fixed 10 lookup_row)
  
def lookup_29 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 30 name: "pi part range check"
  (c.get_advice 87 row) = (c.get_fixed 10 lookup_row)
  
def lookup_20_to_29 (c: ValidCircuit P P_Prime) : Prop :=
  lookup_20 c ∧ lookup_21 c ∧ lookup_22 c ∧ lookup_23 c ∧ lookup_24 c ∧ lookup_25 c ∧ lookup_26 c ∧ lookup_27 c ∧ lookup_28 c ∧ lookup_29 c
def lookup_30 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 31 name: "pi part range check"
  (c.get_advice 88 row) = (c.get_fixed 10 lookup_row)
  
def lookup_31 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 32 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 45 row)))) + (c.get_advice 46 row)) + (-(c.get_advice 47 row)), c.get_advice 65 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_32 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 33 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 46 row)))) + (c.get_advice 47 row)) + (-(c.get_advice 48 row)), c.get_advice 66 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_33 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 34 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 47 row)))) + (c.get_advice 48 row)) + (-(c.get_advice 49 row)), c.get_advice 67 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_34 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 35 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 48 row)))) + (c.get_advice 49 row)) + (-(c.get_advice 45 row)), c.get_advice 68 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_35 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 36 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 49 row)))) + (c.get_advice 45 row)) + (-(c.get_advice 46 row)), c.get_advice 69 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_36 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 37 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 50 row)))) + (c.get_advice 51 row)) + (-(c.get_advice 52 row)), c.get_advice 70 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_37 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 38 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 51 row)))) + (c.get_advice 52 row)) + (-(c.get_advice 53 row)), c.get_advice 71 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_38 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 39 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 52 row)))) + (c.get_advice 53 row)) + (-(c.get_advice 54 row)), c.get_advice 72 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_39 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 40 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 53 row)))) + (c.get_advice 54 row)) + (-(c.get_advice 50 row)), c.get_advice 73 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_30_to_39 (c: ValidCircuit P P_Prime) : Prop :=
  lookup_30 c ∧ lookup_31 c ∧ lookup_32 c ∧ lookup_33 c ∧ lookup_34 c ∧ lookup_35 c ∧ lookup_36 c ∧ lookup_37 c ∧ lookup_38 c ∧ lookup_39 c
def lookup_40 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 41 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 54 row)))) + (c.get_advice 50 row)) + (-(c.get_advice 51 row)), c.get_advice 74 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_41 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 42 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 55 row)))) + (c.get_advice 56 row)) + (-(c.get_advice 57 row)), c.get_advice 75 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_42 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 43 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 56 row)))) + (c.get_advice 57 row)) + (-(c.get_advice 58 row)), c.get_advice 76 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_43 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 44 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 57 row)))) + (c.get_advice 58 row)) + (-(c.get_advice 59 row)), c.get_advice 77 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_44 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 45 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 58 row)))) + (c.get_advice 59 row)) + (-(c.get_advice 55 row)), c.get_advice 78 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_45 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 46 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 59 row)))) + (c.get_advice 55 row)) + (-(c.get_advice 56 row)), c.get_advice 79 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_46 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 47 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 60 row)))) + (c.get_advice 61 row)) + (-(c.get_advice 62 row)), c.get_advice 80 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_47 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 48 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 61 row)))) + (c.get_advice 62 row)) + (-(c.get_advice 63 row)), c.get_advice 81 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_48 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 49 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 62 row)))) + (c.get_advice 63 row)) + (-(c.get_advice 64 row)), c.get_advice 82 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_49 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 50 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 63 row)))) + (c.get_advice 64 row)) + (-(c.get_advice 60 row)), c.get_advice 83 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_40_to_49 (c: ValidCircuit P P_Prime) : Prop :=
  lookup_40 c ∧ lookup_41 c ∧ lookup_42 c ∧ lookup_43 c ∧ lookup_44 c ∧ lookup_45 c ∧ lookup_46 c ∧ lookup_47 c ∧ lookup_48 c ∧ lookup_49 c
def lookup_50 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 51 name: "chi base"
  (((((((((((((((((((((0) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3)) * (8)) + (3))) + (-(((2)) * (c.get_advice 64 row)))) + (c.get_advice 60 row)) + (-(c.get_advice 61 row)), c.get_advice 84 row) = (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
  
def lookup_51 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 52 name: "iota"
  (c.get_advice 89 row, c.get_advice 90 row) = (c.get_fixed 8 lookup_row, c.get_fixed 9 lookup_row)
  
def lookup_52 (c: ValidCircuit P P_Prime) : Prop :=
  ∀ row : ℕ, row < c.usable_rows → ∃ lookup_row : ℕ, lookup_row < c.usable_rows ∧ -- Lookup number 53 name: "squeeze unpack"
  (c.get_advice 92 row, c.get_advice 93 row) = (c.get_fixed 17 lookup_row, c.get_fixed 16 lookup_row)
  
def all_lookups (c: ValidCircuit P P_Prime): Prop :=
  lookup_0_to_9 c ∧ lookup_10_to_19 c ∧ lookup_20_to_29 c ∧ lookup_30_to_39 c ∧ lookup_40_to_49 c ∧ lookup_50 c ∧ lookup_51 c ∧ lookup_52 c
def all_shuffles (c: ValidCircuit P P_Prime) : Prop := true
def meets_constraints (c: ValidCircuit P P_Prime): Prop :=
  sufficient_rows c ∧
  c.1.num_blinding_factors = 58 ∧
  c.1.Selector = selector_func c ∧
  c.1.Fixed = fixed_func c ∧
  c.1.AdvicePhase = advice_phase c ∧
  assertions c  ∧
  all_gates c ∧
  all_copy_constraints c ∧
  all_lookups c ∧
  all_shuffles c ∧
  ∀ col row: ℕ, (row < c.n ∧ row ≥ c.usable_rows) → c.1.Instance col row = c.1.InstanceUnassigned col row
end Scroll.Keccak

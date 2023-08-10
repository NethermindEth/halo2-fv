import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Instance: ℕ → ℕ → ZMod P
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
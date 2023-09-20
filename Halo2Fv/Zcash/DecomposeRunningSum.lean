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
def all_fixed: Prop := true
def selector_func_0 : ℕ → ZMod P :=
  λ row => match row with
    | 0 => 1
    | 1 => 1
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 1
    | 6 => 1
    | 7 => 1
    | 8 => 1
    | 9 => 1
    | 10 => 1
    | 11 => 1
    | 12 => 1
    | 13 => 1
    | 14 => 1
    | 15 => 1
    | 16 => 1
    | 17 => 1
    | 18 => 1
    | 19 => 1
    | 20 => 1
    | 21 => 1
    | 22 => 1
    | 23 => 1
    | 24 => 1
    | 25 => 1
    | 26 => 1
    | 27 => 1
    | 28 => 1
    | 29 => 1
    | 30 => 1
    | 31 => 1
    | 32 => 1
    | 33 => 1
    | 34 => 1
    | 35 => 1
    | 36 => 1
    | 37 => 1
    | 38 => 1
    | 39 => 1
    | 40 => 1
    | 41 => 1
    | 42 => 1
    | 43 => 1
    | 44 => 1
    | 45 => 1
    | 46 => 1
    | 47 => 1
    | 48 => 1
    | 49 => 1
    | 50 => 1
    | 51 => 1
    | 52 => 1
    | 53 => 1
    | 54 => 1
    | 55 => 1
    | 56 => 1
    | 57 => 1
    | 58 => 1
    | 59 => 1
    | 60 => 1
    | 61 => 1
    | 62 => 1
    | 63 => 1
    | 64 => 1
    | 65 => 1
    | 66 => 1
    | 67 => 1
    | 68 => 1
    | 69 => 1
    | 70 => 1
    | 71 => 1
    | 72 => 1
    | 73 => 1
    | 74 => 1
    | 75 => 1
    | 76 => 1
    | 77 => 1
    | 78 => 1
    | 79 => 1
    | 80 => 1
    | 81 => 1
    | 82 => 1
    | 84 => 1
    | 85 => 1
    | 86 => 1
    | 87 => 1
    | 88 => 1
    | 89 => 1
    | 90 => 1
    | 91 => 1
    | 92 => 1
    | 93 => 1
    | 94 => 1
    | 95 => 1
    | 96 => 1
    | 97 => 1
    | 98 => 1
    | 99 => 1
    | 100 => 1
    | 101 => 1
    | 102 => 1
    | 103 => 1
    | 104 => 1
    | 105 => 1
    | 106 => 1
    | 107 => 1
    | 108 => 1
    | 109 => 1
    | 110 => 1
    | 111 => 1
    | 112 => 1
    | 113 => 1
    | 114 => 1
    | 115 => 1
    | 116 => 1
    | 117 => 1
    | 118 => 1
    | 119 => 1
    | 120 => 1
    | 121 => 1
    | 122 => 1
    | 123 => 1
    | 124 => 1
    | 125 => 1
    | 126 => 1
    | 127 => 1
    | 128 => 1
    | 129 => 1
    | 130 => 1
    | 131 => 1
    | 132 => 1
    | 133 => 1
    | 134 => 1
    | 135 => 1
    | 136 => 1
    | 137 => 1
    | 138 => 1
    | 139 => 1
    | 140 => 1
    | 141 => 1
    | 142 => 1
    | 143 => 1
    | 144 => 1
    | 145 => 1
    | 146 => 1
    | 147 => 1
    | 148 => 1
    | 149 => 1
    | 150 => 1
    | 151 => 1
    | 152 => 1
    | 153 => 1
    | 154 => 1
    | 155 => 1
    | 156 => 1
    | 157 => 1
    | 158 => 1
    | 159 => 1
    | 160 => 1
    | 161 => 1
    | 162 => 1
    | 163 => 1
    | 164 => 1
    | 165 => 1
    | 166 => 1
    | _ => 0
def selector_func : ℕ → ℕ → ZMod P :=
  λ col => match col with
    | 0 => selector_func_0
    | _ => λ row => match row with
      | _ => 0
--   λ col row => match col, row with
--     | 0, 0 => 1
--     | _, _ => 0

def advice_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | _, _ => 0
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col, row with
    | _, _ => 0
------GATES-------
def gate_0: Prop := ∀ row : ℕ,  c.Selector 0 row * ((((((((c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)) * (1 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) * (2 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) * (3 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) * (4 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) * (5 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) * (6 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) * (7 - (c.Advice 0 (row) - (c.Advice 0 (row + 1) * 8)))) = 0
def all_gates: Prop := gate_0 c
def meets_constraints: Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func
end Zcash.DecomposeRunningSum

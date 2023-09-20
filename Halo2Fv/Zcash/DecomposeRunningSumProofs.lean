import Halo2Fv.Zcash.DecomposeRunningSum
import Halo2Fv.Util

namespace Zcash.DecomposeRunningSum

lemma gate_0_simplified (c: Circuit P P_Prime) (hGate: gate_0 c) (hSelector: c.Selector 0 row = 1) :
  ((((((Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8 = 0 ∨
              1 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0) ∨
            2 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0) ∨
          3 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0) ∨
        4 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0) ∨
      5 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0) ∨
    6 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0) ∨
  7 - (Circuit.Advice c 0 row - Circuit.Advice c 0 (row + 1) * 8) = 0 := by
  unfold gate_0 at hGate
  specialize hGate row
  rewrite [hSelector, one_mul] at hGate
  have h_NoZeroDivisors : NoZeroDivisors (ZMod P) := ZMod.no_zero_divisors_of_prime P_Prime
  simp only [mul_eq_zero] at hGate
  exact hGate

-- set_option maxRecDepth 10000
-- set_option maxHeartbeats 0
lemma simplified_selector_func {P}: selector_func col row = if col ≠ 0 ∨ row = 83 ∨ row > 166 then 0 else (1: ZMod P) := by
  unfold selector_func
  match col, row with
    | 0, 0 => simp; unfold selector_func_0; simp
    | 0, 1 => simp; unfold selector_func_0; simp
    | 0, 2 => simp; unfold selector_func_0; simp
    | 0, 3 => simp; unfold selector_func_0; simp
    | 0, 4 => simp; unfold selector_func_0; simp
    | 0, 5 => simp; unfold selector_func_0; simp
    | 0, 6 => simp; unfold selector_func_0; simp
    | 0, 7 => simp; unfold selector_func_0; simp
    | 0, 8 => simp; unfold selector_func_0; simp
    | 0, 9 => simp; unfold selector_func_0; simp
    | 0, 10 => simp; unfold selector_func_0; simp
    | 0, 11 => simp; unfold selector_func_0; simp
    | 0, 12 => simp; unfold selector_func_0; simp
    | 0, 13 => simp; unfold selector_func_0; simp
    | 0, 14 => simp; unfold selector_func_0; simp
    | 0, 15 => simp; unfold selector_func_0; simp
    | 0, 16 => simp; unfold selector_func_0; simp
    | 0, 17 => simp; unfold selector_func_0; simp
    | 0, 18 => simp; unfold selector_func_0; simp
    | 0, 19 => simp; unfold selector_func_0; simp
    | 0, 20 => simp; unfold selector_func_0; simp
    | 0, 21 => simp; unfold selector_func_0; simp
    | 0, 22 => simp; unfold selector_func_0; simp
    | 0, 23 => simp; unfold selector_func_0; simp
    | 0, 24 => simp; unfold selector_func_0; simp
    | 0, 25 => simp; unfold selector_func_0; simp
    | 0, 26 => simp; unfold selector_func_0; simp
    | 0, 27 => simp; unfold selector_func_0; simp
    | 0, 28 => simp; unfold selector_func_0; simp
    | 0, 29 => simp; unfold selector_func_0; simp
    | 0, 30 => simp; unfold selector_func_0; simp
    | 0, 31 => simp; unfold selector_func_0; simp
    | 0, 32 => simp; unfold selector_func_0; simp
    | 0, 33 => simp; unfold selector_func_0; simp
    | 0, 34 => simp; unfold selector_func_0; simp
    | 0, 35 => simp; unfold selector_func_0; simp
    | 0, 36 => simp; unfold selector_func_0; simp
    | 0, 37 => simp; unfold selector_func_0; simp
    | 0, 38 => simp; unfold selector_func_0; simp
    | 0, 39 => simp; unfold selector_func_0; simp
    | 0, 40 => simp; unfold selector_func_0; simp
    | 0, 41 => simp; unfold selector_func_0; simp
    | 0, 42 => simp; unfold selector_func_0; simp
    | 0, 43 => simp; unfold selector_func_0; simp
    | 0, 44 => simp; unfold selector_func_0; simp
    | 0, 45 => simp; unfold selector_func_0; simp
    | 0, 46 => simp; unfold selector_func_0; simp
    | 0, 47 => simp; unfold selector_func_0; simp
    | 0, 48 => simp; unfold selector_func_0; simp
    | 0, 49 => simp; unfold selector_func_0; simp
    | 0, 50 => simp; unfold selector_func_0; simp
    | 0, 51 => simp; unfold selector_func_0; simp
    | 0, 52 => simp; unfold selector_func_0; simp
    | 0, 53 => simp; unfold selector_func_0; simp
    | 0, 54 => simp; unfold selector_func_0; simp
    | 0, 55 => simp; unfold selector_func_0; simp
    | 0, 56 => simp; unfold selector_func_0; simp
    | 0, 57 => simp; unfold selector_func_0; simp
    | 0, 58 => simp; unfold selector_func_0; simp
    | 0, 59 => simp; unfold selector_func_0; simp
    | 0, 60 => simp; unfold selector_func_0; simp
    | 0, 61 => simp; unfold selector_func_0; simp
    | 0, 62 => simp; unfold selector_func_0; simp
    | 0, 63 => simp; unfold selector_func_0; simp
    | 0, 64 => simp; unfold selector_func_0; simp
    | 0, 65 => simp; unfold selector_func_0; simp
    | 0, 66 => simp; unfold selector_func_0; simp
    | 0, 67 => simp; unfold selector_func_0; simp
    | 0, 68 => simp; unfold selector_func_0; simp
    | 0, 69 => simp; unfold selector_func_0; simp
    | 0, 70 => simp; unfold selector_func_0; simp
    | 0, 71 => simp; unfold selector_func_0; simp
    | 0, 72 => simp; unfold selector_func_0; simp
    | 0, 73 => simp; unfold selector_func_0; simp
    | 0, 74 => simp; unfold selector_func_0; simp
    | 0, 75 => simp; unfold selector_func_0; simp
    | 0, 76 => simp; unfold selector_func_0; simp
    | 0, 77 => simp; unfold selector_func_0; simp
    | 0, 78 => simp; unfold selector_func_0; simp
    | 0, 79 => simp; unfold selector_func_0; simp
    | 0, 80 => simp; unfold selector_func_0; simp
    | 0, 81 => simp; unfold selector_func_0; simp
    | 0, 82 => simp; unfold selector_func_0; simp
    | 0, 84 => simp; unfold selector_func_0; simp
    | 0, 85 => simp; unfold selector_func_0; simp
    | 0, 86 => simp; unfold selector_func_0; simp
    | 0, 87 => simp; unfold selector_func_0; simp
    | 0, 88 => simp; unfold selector_func_0; simp
    | 0, 89 => simp; unfold selector_func_0; simp
    | 0, 90 => simp; unfold selector_func_0; simp
    | 0, 91 => simp; unfold selector_func_0; simp
    | 0, 92 => simp; unfold selector_func_0; simp
    | 0, 93 => simp; unfold selector_func_0; simp
    | 0, 94 => simp; unfold selector_func_0; simp
    | 0, 95 => simp; unfold selector_func_0; simp
    | 0, 96 => simp; unfold selector_func_0; simp
    | 0, 97 => simp; unfold selector_func_0; simp
    | 0, 98 => simp; unfold selector_func_0; simp
    | 0, 99 => simp; unfold selector_func_0; simp
    | 0, 100 => simp; unfold selector_func_0; simp
    | 0, 101 => simp; unfold selector_func_0; simp
    | 0, 102 => simp; unfold selector_func_0; simp
    | 0, 103 => simp; unfold selector_func_0; simp
    | 0, 104 => simp; unfold selector_func_0; simp
    | 0, 105 => simp; unfold selector_func_0; simp
    | 0, 106 => simp; unfold selector_func_0; simp
    | 0, 107 => simp; unfold selector_func_0; simp
    | 0, 108 => simp; unfold selector_func_0; simp
    | 0, 109 => simp; unfold selector_func_0; simp
    | 0, 110 => simp; unfold selector_func_0; simp
    | 0, 111 => simp; unfold selector_func_0; simp
    | 0, 112 => simp; unfold selector_func_0; simp
    | 0, 113 => simp; unfold selector_func_0; simp
    | 0, 114 => simp; unfold selector_func_0; simp
    | 0, 115 => simp; unfold selector_func_0; simp
    | 0, 116 => simp; unfold selector_func_0; simp
    | 0, 117 => simp; unfold selector_func_0; simp
    | 0, 118 => simp; unfold selector_func_0; simp
    | 0, 119 => simp; unfold selector_func_0; simp
    | 0, 120 => simp; unfold selector_func_0; simp
    | 0, 121 => simp; unfold selector_func_0; simp
    | 0, 122 => simp; unfold selector_func_0; simp
    | 0, 123 => simp; unfold selector_func_0; simp
    | 0, 124 => simp; unfold selector_func_0; simp
    | 0, 125 => simp; unfold selector_func_0; simp
    | 0, 126 => simp; unfold selector_func_0; simp
    | 0, 127 => simp; unfold selector_func_0; simp
    | 0, 128 => simp; unfold selector_func_0; simp
    | 0, 129 => simp; unfold selector_func_0; simp
    | 0, 130 => simp; unfold selector_func_0; simp
    | 0, 131 => simp; unfold selector_func_0; simp
    | 0, 132 => simp; unfold selector_func_0; simp
    | 0, 133 => simp; unfold selector_func_0; simp
    | 0, 134 => simp; unfold selector_func_0; simp
    | 0, 135 => simp; unfold selector_func_0; simp
    | 0, 136 => simp; unfold selector_func_0; simp
    | 0, 137 => simp; unfold selector_func_0; simp
    | 0, 138 => simp; unfold selector_func_0; simp
    | 0, 139 => simp; unfold selector_func_0; simp
    | 0, 140 => simp; unfold selector_func_0; simp
    | 0, 141 => simp; unfold selector_func_0; simp
    | 0, 142 => simp; unfold selector_func_0; simp
    | 0, 143 => simp; unfold selector_func_0; simp
    | 0, 144 => simp; unfold selector_func_0; simp
    | 0, 145 => simp; unfold selector_func_0; simp
    | 0, 146 => simp; unfold selector_func_0; simp
    | 0, 147 => simp; unfold selector_func_0; simp
    | 0, 148 => simp; unfold selector_func_0; simp
    | 0, 149 => simp; unfold selector_func_0; simp
    | 0, 150 => simp; unfold selector_func_0; simp
    | 0, 151 => simp; unfold selector_func_0; simp
    | 0, 152 => simp; unfold selector_func_0; simp
    | 0, 153 => simp; unfold selector_func_0; simp
    | 0, 154 => simp; unfold selector_func_0; simp
    | 0, 155 => simp; unfold selector_func_0; simp
    | 0, 156 => simp; unfold selector_func_0; simp
    | 0, 157 => simp; unfold selector_func_0; simp
    | 0, 158 => simp; unfold selector_func_0; simp
    | 0, 159 => simp; unfold selector_func_0; simp
    | 0, 160 => simp; unfold selector_func_0; simp
    | 0, 161 => simp; unfold selector_func_0; simp
    | 0, 162 => simp; unfold selector_func_0; simp
    | 0, 163 => simp; unfold selector_func_0; simp
    | 0, 164 => simp; unfold selector_func_0; simp
    | 0, 165 => simp; unfold selector_func_0; simp
    | 0, 166 => simp; unfold selector_func_0; simp
    | 0, _ => simp; unfold selector_func_0; simp
    | x+1, _ => simp

lemma A {P}: selector_func (x+1) y = (0: ZMod P) := by
  unfold selector_func
  simp

  

  -- rewrite [←ZMod.val_eq_zero, ←ZMod.val_eq_zero, ←ZMod.val_eq_zero, ←ZMod.val_eq_zero, ←ZMod.val_eq_zero, ←ZMod.val_eq_zero, ←ZMod.val_eq_zero, ←ZMod.val_eq_zero] at hGate
  -- have P_NeZero := prime_NeZero P_Prime
  -- rewrite [sub_eq_add_neg, ZMod.val_add] at hGate
  -- simp [*] at hGate
  -- -- rewrite [of_mod_eq_zero]
  -- sorry
  
  -- rewrite [ZMod.val_nat_cast] at hGate
  -- have h_Roots :
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 1) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 2) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 3) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 4) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 5) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 6) ∨
  --   (c.Advice 0 row = c.Advice 0 (row + 1) * 8 + 7) := by
  --   duplicate hGate
  --   simp only [h_NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero, hGate]
  --   aesop

end Zcash.DecomposeRunningSum
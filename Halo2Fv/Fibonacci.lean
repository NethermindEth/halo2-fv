import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace Fibonacci

  structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
    Instance: ℕ → ℕ → ZMod P
    Advice: ℕ → ℕ → ZMod P
    Fixed: ℕ → ℕ → ZMod P
    Selector: ℕ → ℕ → ZMod P

  variable {P: ℕ} {P_Prime: Nat.Prime P} (c: Circuit P P_Prime)

  --REGION: first row
  def selector_0_0: Prop := c.Selector 0 0 = 1
  --Annotation: f(0)
  def advice_0_0: Prop := c.Advice 0 0 = c.Instance 0 0
  def copy_0: Prop := c.Advice 0 0 = c.Instance 0 0
  --Annotation: f(1)
  def advice_1_0: Prop := c.Advice 1 0 = c.Instance 0 1
  def copy_1: Prop := c.Advice 1 0 = c.Instance 0 1
  --Annotation: a + b
  def advice_2_0: Prop := c.Advice 2 0 = (c.Instance 0 0) + (c.Instance 0 1)
  --EXITED REGION: first row
  --REGION: next row
  def selector_0_1: Prop := c.Selector 0 1 = 1
  --Annotation: a
  def advice_0_1: Prop := c.Advice 0 1 = c.Instance 0 1
  def copy_2: Prop := c.Advice 0 1 = c.Advice 1 0
  --Annotation: b
  def advice_1_1: Prop := c.Advice 1 1 = (c.Instance 0 0) + (c.Instance 0 1)
  def copy_3: Prop := c.Advice 1 1 = c.Advice 2 0
  --Annotation: c
  def advice_2_1: Prop := c.Advice 2 1 = (c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))
  --EXITED REGION: next row
  --REGION: next row
  def selector_0_2: Prop := c.Selector 0 2 = 1
  --Annotation: a
  def advice_0_2: Prop := c.Advice 0 2 = (c.Instance 0 0) + (c.Instance 0 1)
  def copy_4: Prop := c.Advice 0 2 = c.Advice 2 0
  --Annotation: b
  def advice_1_2: Prop := c.Advice 1 2 = (c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))
  def copy_5: Prop := c.Advice 1 2 = c.Advice 2 1
  --Annotation: c
  def advice_2_2: Prop := c.Advice 2 2 = ((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))
  --EXITED REGION: next row
  --REGION: next row
  def selector_0_3: Prop := c.Selector 0 3 = 1
  --Annotation: a
  def advice_0_3: Prop := c.Advice 0 3 = (c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))
  def copy_6: Prop := c.Advice 0 3 = c.Advice 2 1
  --Annotation: b
  def advice_1_3: Prop := c.Advice 1 3 = ((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))
  def copy_7: Prop := c.Advice 1 3 = c.Advice 2 2
  --Annotation: c
  def advice_2_3: Prop := c.Advice 2 3 = ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))
  --EXITED REGION: next row
  --REGION: next row
  def selector_0_4: Prop := c.Selector 0 4 = 1
  --Annotation: a
  def advice_0_4: Prop := c.Advice 0 4 = ((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))
  def copy_8: Prop := c.Advice 0 4 = c.Advice 2 2
  --Annotation: b
  def advice_1_4: Prop := c.Advice 1 4 = ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))
  def copy_9: Prop := c.Advice 1 4 = c.Advice 2 3
  --Annotation: c
  def advice_2_4: Prop := c.Advice 2 4 = (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))
  --EXITED REGION: next row
  --REGION: next row
  def selector_0_5: Prop := c.Selector 0 5 = 1
  --Annotation: a
  def advice_0_5: Prop := c.Advice 0 5 = ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))
  def copy_10: Prop := c.Advice 0 5 = c.Advice 2 3
  --Annotation: b
  def advice_1_5: Prop := c.Advice 1 5 = (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))
  def copy_11: Prop := c.Advice 1 5 = c.Advice 2 4
  --Annotation: c
  def advice_2_5: Prop := c.Advice 2 5 = (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))
  --EXITED REGION: next row
  --REGION: next row
  def selector_0_6: Prop := c.Selector 0 6 = 1
  --Annotation: a
  def advice_0_6: Prop := c.Advice 0 6 = (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))
  def copy_12: Prop := c.Advice 0 6 = c.Advice 2 4
  --Annotation: b
  def advice_1_6: Prop := c.Advice 1 6 = (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))
  def copy_13: Prop := c.Advice 1 6 = c.Advice 2 5
  --Annotation: c
  def advice_2_6: Prop := c.Advice 2 6 = ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))) + ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))))
  --EXITED REGION: next row
  --REGION: next row
  def selector_0_7: Prop := c.Selector 0 7 = 1
  --Annotation: a
  def advice_0_7: Prop := c.Advice 0 7 = (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))
  def copy_14: Prop := c.Advice 0 7 = c.Advice 2 5
  --Annotation: b
  def advice_1_7: Prop := c.Advice 1 7 = ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))) + ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))))
  def copy_15: Prop := c.Advice 1 7 = c.Advice 2 6
  --Annotation: c
  def advice_2_7: Prop := c.Advice 2 7 = ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))) + (((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))))) + ((((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))) + ((((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1)))) + (((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))) + (((c.Instance 0 0) + (c.Instance 0 1)) + ((c.Instance 0 1) + ((c.Instance 0 0) + (c.Instance 0 1))))))))
  --EXITED REGION: next row
  def copy_16: Prop := c.Advice 2 7 = c.Instance 0 2
  ------GATES-------
  def gate_0: Prop := ∀ row : ℕ, c.Selector 0 row * (c.Advice 0 (row) + c.Advice 1 (row) - c.Advice 2 (row)) = 0



  def all_advice: Prop :=
    advice_0_0 c ∧ advice_1_0 c ∧ advice_2_0 c ∧
    advice_0_1 c ∧ advice_1_1 c ∧ advice_2_1 c ∧
    advice_0_2 c ∧ advice_1_2 c ∧ advice_2_2 c ∧
    advice_0_3 c ∧ advice_1_3 c ∧ advice_2_3 c ∧
    advice_0_4 c ∧ advice_1_4 c ∧ advice_2_4 c ∧
    advice_0_5 c ∧ advice_1_5 c ∧ advice_2_5 c ∧
    advice_0_6 c ∧ advice_1_6 c ∧ advice_2_6 c ∧
    advice_0_7 c ∧ advice_1_7 c ∧ advice_2_7 c

  def all_copy_constraints : Prop :=
    copy_0 c ∧
    copy_1 c ∧
    copy_2 c ∧
    copy_3 c ∧
    copy_4 c ∧
    copy_5 c ∧
    copy_6 c ∧
    copy_7 c ∧
    copy_8 c ∧
    copy_9 c ∧
    copy_10 c ∧
    copy_11 c ∧
    copy_12 c ∧
    copy_13 c ∧
    copy_14 c ∧
    copy_15 c ∧
    copy_16 c

  def all_gates : Prop :=
    gate_0 c

  def selector_0_n : Prop := ∀ row : ℕ, row > 7 → c.Selector 0 row = 0
  def all_selectors : Prop :=
    selector_0_0 c ∧
    selector_0_1 c ∧
    selector_0_2 c ∧
    selector_0_3 c ∧
    selector_0_4 c ∧
    selector_0_5 c ∧
    selector_0_6 c ∧
    selector_0_7 c ∧
    selector_0_n c

end Fibonacci

-- lemma TEMP : (1: ZMod P) + (1: ZMod P) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P))) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P)) + ((1: ZMod P) + (1: ZMod P) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P))))) +
--     ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P)) + ((1: ZMod P) + (1: ZMod P) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P)))) + ((1: ZMod P) + (1: ZMod P) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P))) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P)) + ((1: ZMod P) + (1: ZMod P) + ((1: ZMod P) + ((1: ZMod P) + (1: ZMod P))))))) = (34: ZMod P) := by
--       have h: P = 37 := by sorry
--       simp [add_eq_of_eq_sub, h]
--       library_search

-- lemma TEMP: (1: ZMod P) + (1: ZMod P) = (2: ZMod P) := by
--   rewrite [←ZMod.val_add]

-- -- all_advice c ∧ all_selectors c ∧ all_copy_constraints c ∧ all_gates c
-- theorem constraints_of_witness (hI_0: c.Instance 0 0 = 0) (hI_1: c.Instance 0 1 = 1) (hI_1: c.Instance 0 2 = 34) (hS_0_rest: ∀ row : ℕ, row > 7 → c.Selector 0 row = 0) : (all_advice c ∧ all_selectors c) → all_copy_constraints c ∧ all_gates c := by
--   unfold all_advice
--   unfold advice_0_0 advice_0_1 advice_0_2 advice_0_3 advice_0_4 advice_0_5 advice_0_6 advice_0_7
--   unfold advice_1_0 advice_1_1 advice_1_2 advice_1_3 advice_1_4 advice_1_5 advice_1_6 advice_1_7
--   unfold advice_2_0 advice_2_1 advice_2_2 advice_2_3 advice_2_4 advice_2_5 advice_2_6 advice_2_7
--   unfold all_selectors
--   unfold selector_0_0 selector_0_1 selector_0_2 selector_0_3 selector_0_4 selector_0_5 selector_0_6 selector_0_7
--   intro ⟨
--     ⟨
--       hA_0_0, hA_1_0, hA_2_0,
--       hA_0_1, hA_1_1, hA_2_1,
--       hA_0_2, hA_1_2, hA_2_2,
--       hA_0_3, hA_1_3, hA_2_3,
--       hA_0_4, hA_1_4, hA_2_4,
--       hA_0_5, hA_1_5, hA_2_5,
--       hA_0_6, hA_1_6, hA_2_6,
--       hA_0_7, hA_1_7, hA_2_7
--     ⟩,
--     ⟨
--       hS_0_0,
--       hS_0_1,
--       hS_0_2,
--       hS_0_3,
--       hS_0_4,
--       hS_0_5,
--       hS_0_6,
--       hS_0_7
--     ⟩
--   ⟩
--   unfold all_copy_constraints
--   unfold copy_0 copy_1 copy_2 copy_3 copy_4 copy_5 copy_6 copy_7 copy_8 copy_9 copy_10 copy_11 copy_12 copy_13 copy_14 copy_15 copy_16
--   unfold all_gates
--   unfold gate_0
--   simp [*]
--   split_ands
--   . simp [TEMP]
--   . intro row
--     by_cases hRow: row>7
--     . simp [*]
--     . match row with
--         | 0 => aesop
--         | 1 => aesop
--         | 2 => aesop
--         | 3 => aesop
--         | 4 => aesop
--         | 5 => aesop
--         | 6 => aesop
--         | 7 => aesop
--         | x+8 => simp_arith at hRow
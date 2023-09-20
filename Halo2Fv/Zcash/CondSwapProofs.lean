import Halo2Fv.Zcash.CondSwap
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.NeZero
import Halo2Fv.Util


namespace Zcash.CondSwap

  def spec (c: Circuit P P_Prime): Prop :=
    ( (c.Advice 4 1).val = 0 ∧ (c.Advice 2 1).val = (c.Advice 0 0).val ∧ (c.Advice 3 1).val = (c.Advice 1 1).val ) ∨
    ( (c.Advice 4 1).val = 1 ∧ (c.Advice 2 1).val = (c.Advice 1 1).val ∧ (c.Advice 3 1).val = (c.Advice 0 0).val )

  theorem spec_of_constraints (c: Circuit P P_Prime) : meets_constraints c → spec c := by
    intro ⟨
      hSelector,
      ⟨hGate_0, hGate_1, hGate_2⟩,
      hC,
      _
    ⟩
    unfold gate_0 at hGate_0
    unfold gate_1 at hGate_1
    unfold gate_2 at hGate_2
    unfold all_copy_constraints copy_0 at hC
    unfold selector_func at hSelector
    unfold spec
  --   have hP: P ≥ 2 := by simp [Nat.Prime.two_le, *]
    have hBinary: (c.Advice 4 1).val = 0 ∨ (c.Advice 4 1).val = 1 := by
      have h: c.Selector 0 1 * (c.Advice 4 1 * (1 - c.Advice 4 1)) = 0 := by
        apply hGate_2
      simp only [hSelector, one_mul] at h
      exact zero_or_one (c.Advice 4 1) P_Prime h
    cases hBinary with
      | inl hZero =>
        rewrite [hZero]
        simp
        apply And.intro
        . have h: c.Selector 0 1 * (c.Advice 2 1 - (c.Advice 4 1 * c.Advice 1 1 + (1 - c.Advice 4 1) * c.Advice 0 1)) = 0 := by
            apply hGate_0
          simp only [hSelector, one_mul] at h
          simp at hZero
          simp [hZero] at h
          simp [sub_eq_zero] at h
          rw [h, hC]
        . have h: c.Selector 0 1 * (c.Advice 3 1 - (c.Advice 4 1 * c.Advice 0 1 + (1 - c.Advice 4 1) * c.Advice 1 1)) = 0 := by
            apply hGate_1
          simp only [hSelector, one_mul] at h
          simp at hZero
          simp [hZero] at h
          simp [sub_eq_zero] at h
          rw [h]
      | inr hOne =>
        rewrite [hOne]
        simp
        apply And.intro
        . have h: c.Selector 0 1 * (c.Advice 2 1 - (c.Advice 4 1 * c.Advice 1 1 + (1 - c.Advice 4 1) * c.Advice 0 1)) = 0 := by
            apply hGate_0
          simp only [hSelector, one_mul, sub_eq_zero] at h
          have P_NeZero : NeZero P := prime_NeZero P_Prime
          rewrite [h, ZMod.val_add, mul_val_one (Circuit.Advice c 4 1) (Circuit.Advice c 1 1) P_Prime hOne, ZMod.val_mul]
          rewrite [val_one_sub_val_one (Circuit.Advice c 4 1) P_Prime hOne, zero_mul, Nat.zero_mod, add_zero]
          rw [Nat.mod_eq_of_lt]
          apply ZMod.val_lt
        . have h: c.Selector 0 1 * (c.Advice 3 1 - (c.Advice 4 1 * c.Advice 0 1 + (1 - c.Advice 4 1) * c.Advice 1 1)) = 0 := by
            apply hGate_1
          simp only [hSelector, one_mul, hOne, hC, sub_eq_zero] at h
          have P_NeZero: NeZero P := prime_NeZero P_Prime
          rewrite [h, ZMod.val_add, mul_val_one (Circuit.Advice c 4 1) (Circuit.Advice c 0 0) P_Prime hOne, ZMod.val_mul]
          rewrite [val_one_sub_val_one (Circuit.Advice c 4 1) P_Prime hOne, zero_mul, Nat.zero_mod, add_zero]
          rw [Nat.mod_eq_of_lt]
          apply ZMod.val_lt

end Zcash.CondSwap

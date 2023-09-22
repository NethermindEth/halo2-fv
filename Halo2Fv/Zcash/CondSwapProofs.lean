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
    unfold meets_constraints all_gates gate_0 gate_1 gate_2 all_copy_constraints copy_0 selector_func spec
    intro ⟨
      hSelector,
      ⟨hGate_0, hGate_1, hGate_2⟩,
      hC,
      _
    ⟩
    have hBinary: (c.Advice 4 1).val = 0 ∨ (c.Advice 4 1).val = 1 :=
      zero_or_one (c.Advice 4 1) P_Prime 
        (by {
          simp [hSelector, hGate_2 1]
          
        })
      -- specialize hGate_2 1
      -- simp only [hSelector, one_mul] at hGate_2
      -- exact zero_or_one (c.Advice 4 1) P_Prime hGate_2
    specialize hGate_0 1
    specialize hGate_1 1
    rcases hBinary with hFlag | hFlag <;> simp only [hSelector, one_mul, sub_eq_zero, hFlag] at hGate_0 hGate_1
    · aesop
    · have P_NeZero : NeZero P := prime_NeZero P_Prime
      simp [
          hGate_0, hGate_1, 
          ZMod.val_add,
          hC, 
          hFlag,
          P_Prime,
          mul_val_one,
          ZMod.val_mul,
          val_one_sub_val_one,
          ZMod.val_lt,
          Nat.mod_eq_of_lt
        ]
      

end Zcash.CondSwap

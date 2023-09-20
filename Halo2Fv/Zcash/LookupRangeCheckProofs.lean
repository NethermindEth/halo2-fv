import Halo2Fv.Util

namespace Zcash.LookupRangeCheck

  theorem assertion1 {P} (P_Prime: Nat.Prime P) : (((((((1152921504606846976: ZMod P) * ((1024:ZMod P).inv)) * ((1024:ZMod P).inv)) * ((1024:ZMod P).inv)) * ((1024:ZMod P).inv)) * ((1024:ZMod P).inv)) * ((1024:ZMod P).inv)).val = 1 := by
    have hMul: (1152921504606846976: ZMod P).val = ZMod.val (1 * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P)) := by
      norm_num
    have hMulInv1 : ((1152921504606846976: ZMod P) * ((1024:ZMod P).inv)).val = ZMod.val (1 * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P)) := by
      have h: ((1152921504606846976: ZMod P) * ((1024:ZMod P).inv)).val * (1024: ZMod P).val % P = ZMod.val (1 * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P) * (1024:ZMod P)) * (1024 % P) % P := by
        rewrite [←ZMod.val_mul, mul_assoc]
        rewrite [←inv_of_inv, inv_mul_eq_one_of_prime P_Prime 1024, mul_one]
        rewrite [ZMod.val_nat_cast]
        -- have hP_nonZero : P ≠ 0 := (prime_NeZero P_Prime).out
        -- simp [ZMod.inv, hP_nonZero]



end Zcash.LookupRangeCheck
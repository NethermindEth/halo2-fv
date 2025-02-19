import Examples.Scroll.Keccak.Spec.IsFinal
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.FirstRow
  lemma gate_126_is_final_disabled_on_first_row (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_126 c):
    is_final_disabled_on_first_row c
  := by
    unfold is_final_disabled_on_first_row
    unfold gate_126 at hgate
    replace hgate := hgate 0
    simp only [ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1, ite_cond_eq_true, one_mul] at hgate
    simp only [to_is_final] at hgate
    assumption

end Keccak.Gates.FirstRow

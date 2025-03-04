import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.Padding
  lemma gate_154_padding_start_intermediate_byte_last_byte (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_154 c):
    is_paddings c 17 7 = 1 →
    (input_bytes c 17).1[7]? = .some (8, is_first_padding c 17 7 + 128)
  := by
    unfold gate_154 at hgate
    intro h_is_padding
    replace hgate := hgate 204
    simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_6_q_padding_last, Selectors.q_padding_last] at hgate
    simp [is_paddings, cell_manager_to_raw] at h_is_padding
    rewrite [h_is_padding, one_mul] at hgate
    simp only [input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
    simp [word_parts_known, List.getElem?_map, List.getElem?_enum]
    simp [is_first_padding, is_paddings, is_padding_prev, h_is_padding, cell_manager_to_raw]
    simp [add_eq_zero_iff_eq_neg] at hgate
    rw [sub_eq_add_neg, hgate]

end Keccak.Gates.Padding

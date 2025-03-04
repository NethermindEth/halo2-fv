import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  lemma input_bytes_lentgh: (input_bytes c round).1.length = 8 := by
    unfold input_bytes Transform.split_expr Split.expr_res
    simp [keccak_constants, word_parts_known]

  def get_input_byte_expr (c: ValidCircuit P P_Prime) (round: ℕ): (Fin 8) → ZMod P
    | x => (input_bytes c round).1[x].2

  lemma get_input_byte_expr_0: get_input_byte_expr c round 0 = cell_manager c round 72 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
  lemma get_input_byte_expr_1: get_input_byte_expr c round 1 = cell_manager c round 73 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
  lemma get_input_byte_expr_2: get_input_byte_expr c round 2 = cell_manager c round 74 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]
  lemma get_input_byte_expr_3: get_input_byte_expr c round 3 = cell_manager c round 75 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]; rfl
  lemma get_input_byte_expr_4: get_input_byte_expr c round 4 = cell_manager c round 76 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]; rfl
  lemma get_input_byte_expr_5: get_input_byte_expr c round 5 = cell_manager c round 77 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]; rfl
  lemma get_input_byte_expr_6: get_input_byte_expr c round 6 = cell_manager c round 78 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]; rfl
  lemma get_input_byte_expr_7: get_input_byte_expr c round 7 = cell_manager c round 79 := by
    simp [get_input_byte_expr, input_bytes, Transform.split_expr, keccak_constants, Split.expr_res]; rfl
end Keccak

import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  @[to_os] lemma t_1 : Decode.expr
      [(3, cell_manager c round 216), (3, cell_manager c round 217), (3, cell_manager c round 218),
        (3, cell_manager c round 219), (3, cell_manager c round 220), (3, cell_manager c round 221),
        (3, cell_manager c round 222), (3, cell_manager c round 223), (3, cell_manager c round 224),
        (3, cell_manager c round 225), (3, cell_manager c round 226), (3, cell_manager c round 227),
        (3, cell_manager c round 228), (3, cell_manager c round 229), (3, cell_manager c round 230),
        (3, cell_manager c round 231), (3, cell_manager c round 232), (3, cell_manager c round 233),
        (3, cell_manager c round 234), (3, cell_manager c round 235), (3, cell_manager c round 236),
        (1, cell_manager c round 237)] +
    Decode.expr
      [(1, cell_manager c round 281), (3, cell_manager c round 260), (3, cell_manager c round 261),
        (3, cell_manager c round 262), (3, cell_manager c round 263), (3, cell_manager c round 264),
        (3, cell_manager c round 265), (3, cell_manager c round 266), (3, cell_manager c round 267),
        (3, cell_manager c round 268), (3, cell_manager c round 269), (3, cell_manager c round 270),
        (3, cell_manager c round 271), (3, cell_manager c round 272), (3, cell_manager c round 273),
        (3, cell_manager c round 274), (3, cell_manager c round 275), (3, cell_manager c round 276),
        (3, cell_manager c round 277), (3, cell_manager c round 278), (3, cell_manager c round 279),
        (3, cell_manager c round 280)] = t c round 1
  := by
    have h: (↑(4: Fin 5)) = (4: ℕ) := rfl
    simp only [t]
    congr
    . simp [bc, Transform.split_expr, h]
      simp [Split.expr_res, part_size_c, keccak_constants, word_parts_known]
    . simp [part_size_c, keccak_constants, get_rotate_count]
      simp [bc, keccak_constants, part_size_c, Transform.split_expr, Split.expr_res, word_parts_known]
      simp [List.rotateRight]

end Keccak

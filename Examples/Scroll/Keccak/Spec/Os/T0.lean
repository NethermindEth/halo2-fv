import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  @[to_os] lemma t_0 : Decode.expr
        [(3, cell_manager c round 304), (3, cell_manager c round 305), (3, cell_manager c round 306),
          (3, cell_manager c round 307), (3, cell_manager c round 308), (3, cell_manager c round 309),
          (3, cell_manager c round 310), (3, cell_manager c round 311), (3, cell_manager c round 312),
          (3, cell_manager c round 313), (3, cell_manager c round 314), (3, cell_manager c round 315),
          (3, cell_manager c round 316), (3, cell_manager c round 317), (3, cell_manager c round 318),
          (3, cell_manager c round 319), (3, cell_manager c round 320), (3, cell_manager c round 321),
          (3, cell_manager c round 322), (3, cell_manager c round 323), (3, cell_manager c round 324),
          (1, cell_manager c round 325)] +
      Decode.expr
        [(1, cell_manager c round 259), (3, cell_manager c round 238), (3, cell_manager c round 239),
          (3, cell_manager c round 240), (3, cell_manager c round 241), (3, cell_manager c round 242),
          (3, cell_manager c round 243), (3, cell_manager c round 244), (3, cell_manager c round 245),
          (3, cell_manager c round 246), (3, cell_manager c round 247), (3, cell_manager c round 248),
          (3, cell_manager c round 249), (3, cell_manager c round 250), (3, cell_manager c round 251),
          (3, cell_manager c round 252), (3, cell_manager c round 253), (3, cell_manager c round 254),
          (3, cell_manager c round 255), (3, cell_manager c round 256), (3, cell_manager c round 257),
          (3, cell_manager c round 258)] = t c round 0
  := by
    have h: (↑(4: Fin 5)) = (4: ℕ) := rfl
    simp only [t]
    congr
    . simp [bc, Transform.split_expr, h]
      simp [Split.expr, part_size_c, keccak_constants, word_parts_known, List.enum]
    . simp [bc, part_size_c, keccak_constants, get_rotate_count, Transform.split_expr, Split.expr, word_parts_known, List.enum, List.rotateRight]

end Keccak

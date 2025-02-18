import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  @[to_os] lemma t_3 : Decode.expr
      [(3, cell_manager c round 260), (3, cell_manager c round 261), (3, cell_manager c round 262),
        (3, cell_manager c round 263), (3, cell_manager c round 264), (3, cell_manager c round 265),
        (3, cell_manager c round 266), (3, cell_manager c round 267), (3, cell_manager c round 268),
        (3, cell_manager c round 269), (3, cell_manager c round 270), (3, cell_manager c round 271),
        (3, cell_manager c round 272), (3, cell_manager c round 273), (3, cell_manager c round 274),
        (3, cell_manager c round 275), (3, cell_manager c round 276), (3, cell_manager c round 277),
        (3, cell_manager c round 278), (3, cell_manager c round 279), (3, cell_manager c round 280),
        (1, cell_manager c round 281)] +
    Decode.expr
      [(1, cell_manager c round 325), (3, cell_manager c round 304), (3, cell_manager c round 305),
        (3, cell_manager c round 306), (3, cell_manager c round 307), (3, cell_manager c round 308),
        (3, cell_manager c round 309), (3, cell_manager c round 310), (3, cell_manager c round 311),
        (3, cell_manager c round 312), (3, cell_manager c round 313), (3, cell_manager c round 314),
        (3, cell_manager c round 315), (3, cell_manager c round 316), (3, cell_manager c round 317),
        (3, cell_manager c round 318), (3, cell_manager c round 319), (3, cell_manager c round 320),
        (3, cell_manager c round 321), (3, cell_manager c round 322), (3, cell_manager c round 323),
        (3, cell_manager c round 324)] = t c round 3
  := by
    have h: (↑(4: Fin 5)) = (4: ℕ) := rfl
    simp [t, bc, c_parts, Transform.split_expr, Split.expr, part_size_c, get_num_bits_per_theta_c_lookup_val, word_parts_known, List.enum, h, get_rotate_count, List.rotateRight, s]

end Keccak

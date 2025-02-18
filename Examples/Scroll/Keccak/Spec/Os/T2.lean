import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  @[to_os] lemma t_2 : Decode.expr
      [(3, cell_manager c round 238), (3, cell_manager c round 239), (3, cell_manager c round 240),
        (3, cell_manager c round 241), (3, cell_manager c round 242), (3, cell_manager c round 243),
        (3, cell_manager c round 244), (3, cell_manager c round 245), (3, cell_manager c round 246),
        (3, cell_manager c round 247), (3, cell_manager c round 248), (3, cell_manager c round 249),
        (3, cell_manager c round 250), (3, cell_manager c round 251), (3, cell_manager c round 252),
        (3, cell_manager c round 253), (3, cell_manager c round 254), (3, cell_manager c round 255),
        (3, cell_manager c round 256), (3, cell_manager c round 257), (3, cell_manager c round 258),
        (1, cell_manager c round 259)] +
    Decode.expr
      [(1, cell_manager c round 303), (3, cell_manager c round 282), (3, cell_manager c round 283),
        (3, cell_manager c round 284), (3, cell_manager c round 285), (3, cell_manager c round 286),
        (3, cell_manager c round 287), (3, cell_manager c round 288), (3, cell_manager c round 289),
        (3, cell_manager c round 290), (3, cell_manager c round 291), (3, cell_manager c round 292),
        (3, cell_manager c round 293), (3, cell_manager c round 294), (3, cell_manager c round 295),
        (3, cell_manager c round 296), (3, cell_manager c round 297), (3, cell_manager c round 298),
        (3, cell_manager c round 299), (3, cell_manager c round 300), (3, cell_manager c round 301),
        (3, cell_manager c round 302)] = t c round 2
  := by
    have h: (↑(3: Fin 5)) = (3: ℕ) := rfl
    simp [t, bc, c_parts, Transform.split_expr, Split.expr, part_size_c, get_num_bits_per_theta_c_lookup_val, word_parts_known, List.enum, h, get_rotate_count, List.rotateRight, s]

end Keccak

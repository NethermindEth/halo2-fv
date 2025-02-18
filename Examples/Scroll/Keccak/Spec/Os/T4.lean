import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  @[to_os] lemma t_4 : Decode.expr
      [(3, cell_manager c round 282), (3, cell_manager c round 283), (3, cell_manager c round 284),
        (3, cell_manager c round 285), (3, cell_manager c round 286), (3, cell_manager c round 287),
        (3, cell_manager c round 288), (3, cell_manager c round 289), (3, cell_manager c round 290),
        (3, cell_manager c round 291), (3, cell_manager c round 292), (3, cell_manager c round 293),
        (3, cell_manager c round 294), (3, cell_manager c round 295), (3, cell_manager c round 296),
        (3, cell_manager c round 297), (3, cell_manager c round 298), (3, cell_manager c round 299),
        (3, cell_manager c round 300), (3, cell_manager c round 301), (3, cell_manager c round 302),
        (1, cell_manager c round 303)] +
    Decode.expr
      [(1, cell_manager c round 237), (3, cell_manager c round 216), (3, cell_manager c round 217),
        (3, cell_manager c round 218), (3, cell_manager c round 219), (3, cell_manager c round 220),
        (3, cell_manager c round 221), (3, cell_manager c round 222), (3, cell_manager c round 223),
        (3, cell_manager c round 224), (3, cell_manager c round 225), (3, cell_manager c round 226),
        (3, cell_manager c round 227), (3, cell_manager c round 228), (3, cell_manager c round 229),
        (3, cell_manager c round 230), (3, cell_manager c round 231), (3, cell_manager c round 232),
        (3, cell_manager c round 233), (3, cell_manager c round 234), (3, cell_manager c round 235),
        (3, cell_manager c round 236)] = t c round 4
  := by
    have h: (↑(3: Fin 5)) = (3: ℕ) := rfl
    simp [t, bc, c_parts, Transform.split_expr, Split.expr, part_size_c, get_num_bits_per_theta_c_lookup_val, word_parts_known, List.enum, h, get_rotate_count, List.rotateRight, s]

end Keccak

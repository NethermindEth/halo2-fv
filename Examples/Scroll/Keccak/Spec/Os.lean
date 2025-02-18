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
      simp [Split.expr, part_size_c, keccak_constants, word_parts_known, List.enum]
    . simp [part_size_c, keccak_constants, get_rotate_count]
      simp [bc, keccak_constants, part_size_c, Transform.split_expr, Split.expr, word_parts_known, List.enum]
      simp [List.rotateRight]

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

  @[to_os] lemma os_0_0: cell_manager c round 0 + t c round 0 = os c round 0 0 := rfl
  @[to_os] lemma os_0_1: cell_manager c round 1 + t c round 0 = os c round 0 1 := rfl
  @[to_os] lemma os_0_2: cell_manager c round 2 + t c round 0 = os c round 0 2 := rfl
  @[to_os] lemma os_0_3: cell_manager c round 3 + t c round 0 = os c round 0 3 := rfl
  @[to_os] lemma os_0_4: cell_manager c round 4 + t c round 0 = os c round 0 4 := rfl
  @[to_os] lemma os_1_0: cell_manager c round 5 + t c round 1 = os c round 1 0 := rfl
  @[to_os] lemma os_1_1: cell_manager c round 6 + t c round 1 = os c round 1 1 := rfl
  @[to_os] lemma os_1_2: cell_manager c round 7 + t c round 1 = os c round 1 2 := rfl
  @[to_os] lemma os_1_3: cell_manager c round 8 + t c round 1 = os c round 1 3 := rfl
  @[to_os] lemma os_1_4: cell_manager c round 9 + t c round 1 = os c round 1 4 := rfl
  @[to_os] lemma os_2_0: cell_manager c round 10 + t c round 2 = os c round 2 0 := rfl
  @[to_os] lemma os_2_1: cell_manager c round 11 + t c round 2 = os c round 2 1 := rfl
  @[to_os] lemma os_2_2: cell_manager c round 12 + t c round 2 = os c round 2 2 := rfl
  @[to_os] lemma os_2_3: cell_manager c round 13 + t c round 2 = os c round 2 3 := rfl
  @[to_os] lemma os_2_4: cell_manager c round 14 + t c round 2 = os c round 2 4 := rfl
  @[to_os] lemma os_3_0: cell_manager c round 15 + t c round 3 = os c round 3 0 := rfl
  @[to_os] lemma os_3_1: cell_manager c round 16 + t c round 3 = os c round 3 1 := rfl
  @[to_os] lemma os_3_2: cell_manager c round 17 + t c round 3 = os c round 3 2 := rfl
  @[to_os] lemma os_3_3: cell_manager c round 18 + t c round 3 = os c round 3 3 := rfl
  @[to_os] lemma os_3_4: cell_manager c round 19 + t c round 3 = os c round 3 4 := rfl
  @[to_os] lemma os_4_0: cell_manager c round 20 + t c round 4 = os c round 4 0 := rfl
  @[to_os] lemma os_4_1: cell_manager c round 21 + t c round 4 = os c round 4 1 := rfl
  @[to_os] lemma os_4_2: cell_manager c round 22 + t c round 4 = os c round 4 2 := rfl
  @[to_os] lemma os_4_3: cell_manager c round 23 + t c round 4 = os c round 4 3 := rfl
  @[to_os] lemma os_4_4: cell_manager c round 24 + t c round 4 = os c round 4 4 := rfl

end Keccak

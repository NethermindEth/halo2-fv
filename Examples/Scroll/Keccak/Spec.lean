import Examples.Scroll.Keccak.Extraction
import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.Util
import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Selectors
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Examples.Util

namespace Keccak

  def keccak_unusable_rows: ℕ := 59 -- TODO implement using list, this is specific to DEFAULT_KECCAK_ROWS and NUM_BYTES_PER_WORD

  def get_num_bits_per_lookup (range: ℕ): ℕ :=
    Nat.log range (2^KECCAK_DEGREE - keccak_unusable_rows)

  lemma get_num_bits_per_lookup_correct (range: ℕ) (h_range: range ≥ 2):
    range^(get_num_bits_per_lookup range + 1) + keccak_unusable_rows > 2^KECCAK_DEGREE ∧
    range^(get_num_bits_per_lookup range) + keccak_unusable_rows ≤ 2^KECCAK_DEGREE := by
      rewrite [get_num_bits_per_lookup, KECCAK_DEGREE, keccak_unusable_rows]
      simp only [Nat.reducePow, Nat.reduceSub]
      apply And.intro
      . have h: 965 < range ^ (Nat.log range 965 + 1) := by
          rewrite [←Nat.log_mul_base]
          unfold Nat.log
          dsimp only
          rewrite [dite_cond_eq_true]
          rewrite [Nat.mul_div_cancel]
          exact Nat.lt_pow_succ_log_self h_range 965
          linarith
          apply eq_true
          apply And.intro
          linarith
          linarith
          linarith
          decide
        linarith
      . simp only [add_tsub_cancel_right, Nat.reduceLeDiff]
        simp [Nat.pow_log_le_self]

  def get_num_bits_per_absorb_lookup: ℕ := get_num_bits_per_lookup ABSORB_LOOKUP_RANGE
  def get_num_bits_per_base_chi_lookup: ℕ := get_num_bits_per_lookup (max CHI_BASE_LOOKUP_RANGE RHO_PI_LOOKUP_RANGE)
  def get_num_bits_per_theta_c_lookup: ℕ := get_num_bits_per_lookup THETA_C_LOOKUP_RANGE

  @[keccak_constants] lemma get_num_bits_per_absorb_lookup_val: get_num_bits_per_absorb_lookup = 6 := by
    rewrite [get_num_bits_per_absorb_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_base_chi_lookup_val: get_num_bits_per_base_chi_lookup = 4 := by
    rewrite [get_num_bits_per_base_chi_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_theta_c_lookup_val: get_num_bits_per_theta_c_lookup = 3 := by
    rewrite [get_num_bits_per_theta_c_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  namespace Decode
    def expr (parts: List (ℕ × ZMod P)) : ZMod P :=
      List.foldr
        (λ (part: ℕ × ZMod P) (acc: ZMod P) => 2^(BIT_COUNT*part.1) * acc + part.2)
        0
        parts

    @[to_decode] lemma to_decode_nil {P: ℕ}: (0: ZMod P) = expr [] := by rfl
    @[to_decode] lemma to_decode_cons_1 {x: ZMod P}: 8 * expr l + x = expr ((1,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_2 {x: ZMod P}: 64 * expr l + x = expr ((2,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_3 {x: ZMod P}: 512 * expr l + x = expr ((3,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_4 {x: ZMod P}: 4096 * expr l + x = expr ((4,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
  end Decode

  namespace Split
    def expr (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ): List (ℕ × ZMod P) :=
      (WordParts.new target_part_size rot false
      ).enum.map (
        λ (offset, bits) => (bits.length, cell_manager c round (cell_offset + offset))
      )

    def constraint (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ) (input: ZMod P): Prop :=
      Decode.expr (Split.expr c cell_offset round rot target_part_size) = input
  end Split

  namespace SplitUniform
    def input_parts (c: ValidCircuit P P_Prime) (output_cells: List (ZMod P)) (cell_offset round: ℕ) (word: List (List ℕ)) (target_sizes: List ℕ): List (ℕ × ZMod P) :=
      match output_cells, word, target_sizes with
        | o::os, w1::w2::ws, t::ts =>
          if w1.length = t
          then (t, o)::(input_parts c (output_cells := os) cell_offset round (word := w2::ws) (target_sizes := ts))
          else (w1.length, cell_manager c round cell_offset)::(w2.length, cell_manager c round (cell_offset + 1))::(input_parts c (output_cells := os) (cell_offset := cell_offset + 2) round (word := ws) (target_sizes := ts))
        | o::os, _::ws, t::ts =>
          (t, o)::(input_parts c (output_cells := os) cell_offset round (word := ws) (target_sizes := ts))
        | _, _, _ => []

    def rot_parts (c: ValidCircuit P P_Prime) (output_cells: List (ZMod P)) (cell_offset round: ℕ) (word: List (List ℕ)) (target_sizes: List ℕ): Prop :=
      match output_cells, word, target_sizes with
        | o::os, w1::w2::ws, t::ts =>
          if w1.length = t
          then True ∧ rot_parts c (output_cells := os) cell_offset round (word := w2::ws) (target_sizes := ts)
          else ((cell_manager c round cell_offset) + (cell_manager c round (cell_offset + 1)) * (2^(BIT_COUNT * w1.length)) = o) ∧ (rot_parts c (output_cells := os) (cell_offset := cell_offset + 2) round (word := ws) (target_sizes := ts))
        | _::os, _::ws, _::ts =>
          True ∧ rot_parts c (output_cells := os) cell_offset round (word := ws) (target_sizes := ts)
        | [], [], [] => True
        | _, _, _ => False

    def output_parts (output_cells: List (ZMod P)) (target_sizes: List ℕ): List (ℕ × ZMod P) :=
      match output_cells, target_sizes with
        | o::os, t::ts =>
          (t, o)::(output_parts (output_cells := os) (target_sizes := ts))
        | _, _ => []
    def constraint [NeZero K] (c: ValidCircuit P P_Prime) (output_cells: Fin K → ZMod P) (cell_offset round: ℕ) (input: ZMod P) (rot target_part_size: ℕ) :=
      Decode.expr ((input_parts c cell_offset round
        (output_cells := (List.range K).map (λ x: ℕ => output_cells (Fin.ofNat' K x)))
        (word := (WordParts.new target_part_size rot true).rotateRight (get_rotate_count rot target_part_size))
        (target_sizes := target_part_sizes target_part_size)).rotateLeft (get_rotate_count rot target_part_size)) = input ∧
      (rot_parts c cell_offset round
        (output_cells := (List.range K).map (λ x: ℕ => output_cells (Fin.ofNat' K x)))
        (word := (WordParts.new target_part_size rot true).rotateRight (get_rotate_count rot target_part_size))
        (target_sizes := target_part_sizes target_part_size))

    def expr [NeZero K] (output_cells: Fin K → ZMod P) (target_part_size: ℕ):=
      output_parts
        (output_cells := (List.range K).map (λ x: ℕ => output_cells (Fin.ofNat' K x)))
        (target_sizes := target_part_sizes target_part_size)

  end SplitUniform

  namespace Transform
    def split_expr (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ) (transform_offset: ℕ): List (ℕ × ZMod P) :=
      Split.expr c (cell_offset + transform_offset) round rot target_part_size
  end Transform

  section asserts
    -- NOTE: assert comment says DEFAULT_KECCAK_ROWS > (NUM_BYTES_PER_WORD + 1),
    -- but the assert states the following
    lemma get_num_rows_per_round_assert: DEFAULT_KECCAK_ROWS > NUM_BYTES_PER_WORD := by trivial
  end asserts

  def start_new_hash (c: ValidCircuit P P_Prime) (row: ℕ): Prop := c.get_fixed 1 row = 1 ∨ c.get_advice 0 row = 1
  def round_cst (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_fixed 7 row

  def s (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5): ZMod P :=
    cell_manager c round ((5*↑x) + ↑y)
  -- def s_next

  -- TODO: name of round?
  -- TODO row range 12-288
  def absorb_from (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := cell_manager c round 25
  def absorb_data (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := cell_manager c round 26
  def absorb_result (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := cell_manager c round 27 -- bound by gate 1

  -- def absorb_from_next
  -- def absorb_data_next
  -- def absorb_result_next

  def input (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := absorb_from c round + absorb_data c round -- bound by gate 0
  -- absorb_res: lookup_0

  --Process inputs
  -- packed_parts: gate 2
  -- input_bytes: lookup_1

  --Theta
  -- Gates 3,4,5,6,7 handle the constraints for these splits
  def part_size_c := get_num_bits_per_theta_c_lookup
  def c_parts (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 5) : List (ℕ × ZMod P) :=
    Split.expr c round
      (cell_offset := 96 + 22*↑idx)
      (rot := 1)
      (target_part_size := part_size_c)

  def bc (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 5): List (ℕ × ZMod P) :=
    Transform.split_expr c round
      (cell_offset := 96 + 22*↑idx)
      (rot := 1)
      (target_part_size := part_size_c)
      (transform_offset := 120)

  def t (c: ValidCircuit P P_Prime) (round: ℕ) (x: Fin 5) :=
    (Decode.expr (bc c round (x + 4)) + Decode.expr ((bc c round (x+1)).rotateRight (get_rotate_count 1 part_size_c)))

  def os (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5) :=
    s c round x y + t c round x

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
    simp [t, bc, c_parts, Transform.split_expr, Split.expr, part_size_c, get_num_bits_per_theta_c_lookup_val, word_parts_known, List.enum, h, get_rotate_count, List.rotateRight, s]

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
    simp [t, bc, c_parts, Transform.split_expr, Split.expr, part_size_c, get_num_bits_per_theta_c_lookup_val, word_parts_known, List.enum, h, get_rotate_count, List.rotateRight, s]

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

  -- Rho/Pi
  def rho_by_pi_num_word_parts := (target_part_sizes_rot get_num_bits_per_base_chi_lookup 0).length
  @[keccak_constants] lemma rho_by_pi_num_word_parts_val : rho_by_pi_num_word_parts = 16 := by
    simp [rho_by_pi_num_word_parts, get_num_bits_per_base_chi_lookup_val, target_part_sizes, List.length]
  instance : NeZero rho_by_pi_num_word_parts where
    out := by simp [rho_by_pi_num_word_parts, get_num_bits_per_base_chi_lookup_val, target_part_sizes_rot, List.map]
  def rho_pi_chi_cells (c: ValidCircuit P P_Prime) (round: ℕ) (p: Fin 3) (i j: Fin 5) (idx: Fin rho_by_pi_num_word_parts) :=
    let row_idx: ℕ := ↑idx + ↑j * rho_by_pi_num_word_parts + ↑p * 5 * rho_by_pi_num_word_parts
    cell_manager c round (
      336 + --start
      DEFAULT_KECCAK_ROWS*↑i +
      row_idx % DEFAULT_KECCAK_ROWS +
      5 * (row_idx / DEFAULT_KECCAK_ROWS) * DEFAULT_KECCAK_ROWS
    )

  -- line 471
  def squeeze_from (c: ValidCircuit P P_Prime) (round: ℕ):= cell_manager c round 1656

  -- section Gates

  --   section RotPart
  --     lemma gate_9_rot_part (c: ValidCircuit P P_Prime) (hgate_9: gate_9 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 140 row 0 + 2^(BIT_COUNT*1) * c.get_advice_wrapped 140 row 1 =
  --       c.get_advice_wrapped 45 row 8
  --       := by
  --         unfold gate_9 at hgate_9
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_9 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_9 row)))
  --             rewrite [neg_involutive] at hgate_9
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow3, hgate_9]

  --     lemma gate_11_rot_part (c: ValidCircuit P P_Prime) (hgate_11: gate_11 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 140 row 2 + 2^(BIT_COUNT*2) * c.get_advice_wrapped 140 row 3 =
  --       c.get_advice_wrapped 65 row 7
  --       := by
  --         unfold gate_11 at hgate_11
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_11 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_11 row)))
  --             rewrite [neg_involutive] at hgate_11
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow6, hgate_11]

  --     lemma gate_14_rot_part (c: ValidCircuit P P_Prime) (hgate_14: gate_14 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 140 row 4 + 2^(BIT_COUNT*3) * c.get_advice_wrapped 140 row 5 =
  --       c.get_advice_wrapped 55 row 6
  --       := by
  --         unfold gate_14 at hgate_14
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_14 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_14 row)))
  --             rewrite [neg_involutive] at hgate_14
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow9, hgate_14]

  --     lemma gate_18_rot_part (c: ValidCircuit P P_Prime) (hgate_18: gate_18 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 140 row 6 + 2^(BIT_COUNT*2) * c.get_advice_wrapped 140 row 7 =
  --       c.get_advice_wrapped 46 row 9
  --       := by
  --         unfold gate_18 at hgate_18
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_18 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_18 row)))
  --             rewrite [neg_involutive] at hgate_18
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow6, hgate_18]

  --     lemma gate_20_rot_part (c: ValidCircuit P P_Prime) (hgate_20: gate_20 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 140 row 8 + 2^(BIT_COUNT*3) * c.get_advice_wrapped 140 row 9 =
  --       c.get_advice_wrapped 66 row 5
  --       := by
  --         unfold gate_20 at hgate_20
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_20 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_20 row)))
  --             rewrite [neg_involutive] at hgate_20
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow9, hgate_20]

  --     lemma gate_23_rot_part (c: ValidCircuit P P_Prime) (hgate_23: gate_23 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 140 row 10 + 2^(BIT_COUNT*3) * c.get_advice_wrapped 140 row 11 =
  --       c.get_advice_wrapped 42 row 4
  --       := by
  --         unfold gate_23 at hgate_23
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_23 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_23 row)))
  --             rewrite [neg_involutive] at hgate_23
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow9, hgate_23]

  --     lemma gate_25_rot_part (c: ValidCircuit P P_Prime) (hgate_25: gate_25 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 141 row 0 + 2^(BIT_COUNT*2) * c.get_advice_wrapped 141 row 1 =
  --       c.get_advice_wrapped 57 row 2
  --       := by
  --         unfold gate_25 at hgate_25
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_25 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_25 row)))
  --             rewrite [neg_involutive] at hgate_25
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow6, hgate_25]

  --     lemma gate_27_rot_part (c: ValidCircuit P P_Prime) (hgate_27: gate_27 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 141 row 2 + 2^(BIT_COUNT*3) * c.get_advice_wrapped 141 row 3 =
  --       c.get_advice_wrapped 37 row 10
  --       := by
  --         unfold gate_27 at hgate_27
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_27 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_27 row)))
  --             rewrite [neg_involutive] at hgate_27
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow9, hgate_27]

  --     lemma gate_29_rot_part (c: ValidCircuit P P_Prime) (hgate_29: gate_29 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 141 row 4 + 2^(BIT_COUNT*1) * c.get_advice_wrapped 141 row 5 =
  --       c.get_advice_wrapped 52 row 2
  --       := by
  --         unfold gate_29 at hgate_29
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_29 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_29 row)))
  --             rewrite [neg_involutive] at hgate_29
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow3, hgate_29]

  --     lemma gate_31_rot_part (c: ValidCircuit P P_Prime) (hgate_31: gate_31 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 141 row 6 + 2^(BIT_COUNT*3) * c.get_advice_wrapped 141 row 7 =
  --       c.get_advice_wrapped 67 row 1
  --       := by
  --         unfold gate_31 at hgate_31
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_31 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_31 row)))
  --             rewrite [neg_involutive] at hgate_31
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow9, hgate_31]

  --     lemma gate_33_rot_part (c: ValidCircuit P P_Prime) (hgate_33: gate_33 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 141 row 8 + 2^(BIT_COUNT*1) * c.get_advice_wrapped 141 row 9 =
  --       c.get_advice_wrapped 68 row 2
  --       := by
  --         unfold gate_33 at hgate_33
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_33 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_33 row)))
  --             rewrite [neg_involutive] at hgate_33
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow3, hgate_33]

  --     lemma gate_35_rot_part (c: ValidCircuit P P_Prime) (hgate_35: gate_35 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 141 row 10 + 2^(BIT_COUNT*1) * c.get_advice_wrapped 141 row 11 =
  --       c.get_advice_wrapped 48 row 3
  --       := by
  --         unfold gate_35 at hgate_35
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_35 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_35 row)))
  --             rewrite [neg_involutive] at hgate_35
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow3, hgate_35]

  --     lemma gate_37_rot_part (c: ValidCircuit P P_Prime) (hgate_37: gate_37 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 142 row 0 + 2^(BIT_COUNT*3) * c.get_advice_wrapped 142 row 1 =
  --       c.get_advice_wrapped 58 row 3
  --       := by
  --         unfold gate_37 at hgate_37
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_37 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_37 row)))
  --             rewrite [neg_involutive] at hgate_37
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow9, hgate_37]

  --     lemma gate_39_rot_part (c: ValidCircuit P P_Prime) (hgate_39: gate_39 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 142 row 2 + 2^(BIT_COUNT*1) * c.get_advice_wrapped 142 row 3 =
  --       c.get_advice_wrapped 38 row 5
  --       := by
  --         unfold gate_39 at hgate_39
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_39 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_39 row)))
  --             rewrite [neg_involutive] at hgate_39
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow3, hgate_39]

  --     lemma gate_42_rot_part (c: ValidCircuit P P_Prime) (hgate_42: gate_42 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 142 row 4 + 2^(BIT_COUNT*2) * c.get_advice_wrapped 142 row 5 =
  --       c.get_advice_wrapped 54 row 0
  --       := by
  --         unfold gate_42 at hgate_42
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_42 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_42 row)))
  --             rewrite [neg_involutive] at hgate_42
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow6, hgate_42]

  --     lemma gate_44_rot_part (c: ValidCircuit P P_Prime) (hgate_44: gate_44 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 142 row 6 + 2^(BIT_COUNT*2) * c.get_advice_wrapped 142 row 7 =
  --       c.get_advice_wrapped 64 row 4
  --       := by
  --         unfold gate_44 at hgate_44
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_44 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_44 row)))
  --             rewrite [neg_involutive] at hgate_44
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow6, hgate_44]

  --     lemma gate_46_rot_part (c: ValidCircuit P P_Prime) (hgate_46: gate_46 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 142 row 8 + 2^(BIT_COUNT*1) * c.get_advice_wrapped 142 row 9 =
  --       c.get_advice_wrapped 49 row 7
  --       := by
  --         unfold gate_46 at hgate_46
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_46 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_46 row)))
  --             rewrite [neg_involutive] at hgate_46
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow3, hgate_46]

  --     lemma gate_49_rot_part (c: ValidCircuit P P_Prime) (hgate_49: gate_49 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       c.get_advice_wrapped 142 row 10 + 2^(BIT_COUNT*2) * c.get_advice_wrapped 142 row 11 =
  --       c.get_advice_wrapped 39 row 3
  --       := by
  --         unfold gate_49 at hgate_49
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_49 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_49 row)))
  --             rewrite [neg_involutive] at hgate_49
  --             simp only [BIT_COUNT, ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range, Nat.reduceMul, zmod_2pow6, hgate_49]
  --   end RotPart

  --   section NextRowCheck
  --     lemma gate_52_next_row_check (c: ValidCircuit P P_Prime) (hgate_52: gate_52 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (6, c.get_advice_wrapped 144 row 0),
  --         (6, c.get_advice_wrapped 144 row 1),
  --         (6, c.get_advice_wrapped 144 row 2),
  --         (6, c.get_advice_wrapped 144 row 3),
  --         (6, c.get_advice_wrapped 144 row 4),
  --         (6, c.get_advice_wrapped 144 row 5),
  --         (6, c.get_advice_wrapped 144 row 6),
  --         (6, c.get_advice_wrapped 144 row 7),
  --         (6, c.get_advice_wrapped 144 row 8),
  --         (6, c.get_advice_wrapped 144 row 9),
  --         (4, c.get_advice_wrapped 144 row 10),
  --       ] =
  --       c.get_advice_wrapped 7 row 12
  --       := by
  --         unfold gate_52 at hgate_52
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_52 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_52 row)))
  --             rewrite [neg_involutive] at hgate_52
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_52]
  --             clear hgate_52
  --             rfl

  --     lemma gate_53_next_row_check (c: ValidCircuit P P_Prime) (hgate_53: gate_53 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 110 row 4),
  --         (4, c.get_advice_wrapped 110 row 5),
  --         (4, c.get_advice_wrapped 110 row 6),
  --         (4, c.get_advice_wrapped 110 row 7),
  --         (4, c.get_advice_wrapped 110 row 8),
  --         (4, c.get_advice_wrapped 110 row 9),
  --         (4, c.get_advice_wrapped 110 row 10),
  --         (4, c.get_advice_wrapped 110 row 11),
  --         (4, c.get_advice_wrapped 115 row 0),
  --         (4, c.get_advice_wrapped 115 row 1),
  --         (4, c.get_advice_wrapped 115 row 2),
  --         (4, c.get_advice_wrapped 115 row 3),
  --         (4, c.get_advice_wrapped 115 row 4),
  --         (4, c.get_advice_wrapped 115 row 5),
  --         (4, c.get_advice_wrapped 115 row 6),
  --         (4, c.get_advice_wrapped 115 row 7),
  --       ] =
  --       c.get_advice_wrapped 7 row 13
  --       := by
  --         unfold gate_53 at hgate_53
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_53 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_53 row)))
  --             rewrite [neg_involutive] at hgate_53
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_53]
  --             clear hgate_53
  --             rfl

  --     lemma gate_54_next_row_check (c: ValidCircuit P P_Prime) (hgate_54: gate_54 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 115 row 8),
  --         (4, c.get_advice_wrapped 115 row 9),
  --         (4, c.get_advice_wrapped 115 row 10),
  --         (4, c.get_advice_wrapped 115 row 11),
  --         (4, c.get_advice_wrapped 120 row 0),
  --         (4, c.get_advice_wrapped 120 row 1),
  --         (4, c.get_advice_wrapped 120 row 2),
  --         (4, c.get_advice_wrapped 120 row 3),
  --         (4, c.get_advice_wrapped 120 row 4),
  --         (4, c.get_advice_wrapped 120 row 5),
  --         (4, c.get_advice_wrapped 120 row 6),
  --         (4, c.get_advice_wrapped 120 row 7),
  --         (4, c.get_advice_wrapped 120 row 8),
  --         (4, c.get_advice_wrapped 120 row 9),
  --         (4, c.get_advice_wrapped 120 row 10),
  --         (4, c.get_advice_wrapped 120 row 11),
  --       ] =
  --       c.get_advice_wrapped 7 row 14
  --       := by
  --         unfold gate_54 at hgate_54
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_54 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_54 row)))
  --             rewrite [neg_involutive] at hgate_54
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_54]
  --             clear hgate_54
  --             rfl

  --     lemma gate_55_next_row_check (c: ValidCircuit P P_Prime) (hgate_55: gate_55 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 125 row 0),
  --         (4, c.get_advice_wrapped 125 row 1),
  --         (4, c.get_advice_wrapped 125 row 2),
  --         (4, c.get_advice_wrapped 125 row 3),
  --         (4, c.get_advice_wrapped 125 row 4),
  --         (4, c.get_advice_wrapped 125 row 5),
  --         (4, c.get_advice_wrapped 125 row 6),
  --         (4, c.get_advice_wrapped 125 row 7),
  --         (4, c.get_advice_wrapped 125 row 8),
  --         (4, c.get_advice_wrapped 125 row 9),
  --         (4, c.get_advice_wrapped 125 row 10),
  --         (4, c.get_advice_wrapped 125 row 11),
  --         (4, c.get_advice_wrapped 130 row 0),
  --         (4, c.get_advice_wrapped 130 row 1),
  --         (4, c.get_advice_wrapped 130 row 2),
  --         (4, c.get_advice_wrapped 130 row 3),
  --       ] =
  --       c.get_advice_wrapped 7 row 15
  --       := by
  --         unfold gate_55 at hgate_55
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_55 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_55 row)))
  --             rewrite [neg_involutive] at hgate_55
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_55]
  --             clear hgate_55
  --             rfl

  --     lemma gate_56_next_row_check (c: ValidCircuit P P_Prime) (hgate_56: gate_56 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 130 row 4),
  --         (4, c.get_advice_wrapped 130 row 5),
  --         (4, c.get_advice_wrapped 130 row 6),
  --         (4, c.get_advice_wrapped 130 row 7),
  --         (4, c.get_advice_wrapped 130 row 8),
  --         (4, c.get_advice_wrapped 130 row 9),
  --         (4, c.get_advice_wrapped 130 row 10),
  --         (4, c.get_advice_wrapped 130 row 11),
  --         (4, c.get_advice_wrapped 135 row 0),
  --         (4, c.get_advice_wrapped 135 row 1),
  --         (4, c.get_advice_wrapped 135 row 2),
  --         (4, c.get_advice_wrapped 135 row 3),
  --         (4, c.get_advice_wrapped 135 row 4),
  --         (4, c.get_advice_wrapped 135 row 5),
  --         (4, c.get_advice_wrapped 135 row 6),
  --         (4, c.get_advice_wrapped 135 row 7),
  --       ] =
  --       c.get_advice_wrapped 7 row 16
  --       := by
  --         unfold gate_56 at hgate_56
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_56 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_56 row)))
  --             rewrite [neg_involutive] at hgate_56
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_56]
  --             clear hgate_56
  --             rfl

  --     lemma gate_57_next_row_check (c: ValidCircuit P P_Prime) (hgate_57: gate_57 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 106 row 0),
  --         (4, c.get_advice_wrapped 106 row 1),
  --         (4, c.get_advice_wrapped 106 row 2),
  --         (4, c.get_advice_wrapped 106 row 3),
  --         (4, c.get_advice_wrapped 106 row 4),
  --         (4, c.get_advice_wrapped 106 row 5),
  --         (4, c.get_advice_wrapped 106 row 6),
  --         (4, c.get_advice_wrapped 106 row 7),
  --         (4, c.get_advice_wrapped 106 row 8),
  --         (4, c.get_advice_wrapped 106 row 9),
  --         (4, c.get_advice_wrapped 106 row 10),
  --         (4, c.get_advice_wrapped 106 row 11),
  --         (4, c.get_advice_wrapped 111 row 0),
  --         (4, c.get_advice_wrapped 111 row 1),
  --         (4, c.get_advice_wrapped 111 row 2),
  --         (4, c.get_advice_wrapped 111 row 3),
  --       ] =
  --       c.get_advice_wrapped 7 row 17
  --       := by
  --         unfold gate_57 at hgate_57
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_57 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_57 row)))
  --             rewrite [neg_involutive] at hgate_57
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_57]
  --             clear hgate_57
  --             rfl

  --     lemma gate_58_next_row_check (c: ValidCircuit P P_Prime) (hgate_58: gate_58 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 111 row 4),
  --         (4, c.get_advice_wrapped 111 row 5),
  --         (4, c.get_advice_wrapped 111 row 6),
  --         (4, c.get_advice_wrapped 111 row 7),
  --         (4, c.get_advice_wrapped 111 row 8),
  --         (4, c.get_advice_wrapped 111 row 9),
  --         (4, c.get_advice_wrapped 111 row 10),
  --         (4, c.get_advice_wrapped 111 row 11),
  --         (4, c.get_advice_wrapped 116 row 0),
  --         (4, c.get_advice_wrapped 116 row 1),
  --         (4, c.get_advice_wrapped 116 row 2),
  --         (4, c.get_advice_wrapped 116 row 3),
  --         (4, c.get_advice_wrapped 116 row 4),
  --         (4, c.get_advice_wrapped 116 row 5),
  --         (4, c.get_advice_wrapped 116 row 6),
  --         (4, c.get_advice_wrapped 116 row 7),
  --       ] =
  --       c.get_advice_wrapped 7 row 18
  --       := by
  --         unfold gate_58 at hgate_58
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_58 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_58 row)))
  --             rewrite [neg_involutive] at hgate_58
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_58]
  --             clear hgate_58
  --             rfl

  --     lemma gate_59_next_row_check (c: ValidCircuit P P_Prime) (hgate_59: gate_59 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 116 row 8),
  --         (4, c.get_advice_wrapped 116 row 9),
  --         (4, c.get_advice_wrapped 116 row 10),
  --         (4, c.get_advice_wrapped 116 row 11),
  --         (4, c.get_advice_wrapped 121 row 0),
  --         (4, c.get_advice_wrapped 121 row 1),
  --         (4, c.get_advice_wrapped 121 row 2),
  --         (4, c.get_advice_wrapped 121 row 3),
  --         (4, c.get_advice_wrapped 121 row 4),
  --         (4, c.get_advice_wrapped 121 row 5),
  --         (4, c.get_advice_wrapped 121 row 6),
  --         (4, c.get_advice_wrapped 121 row 7),
  --         (4, c.get_advice_wrapped 121 row 8),
  --         (4, c.get_advice_wrapped 121 row 9),
  --         (4, c.get_advice_wrapped 121 row 10),
  --         (4, c.get_advice_wrapped 121 row 11),
  --       ] =
  --       c.get_advice_wrapped 7 row 19
  --       := by
  --         unfold gate_59 at hgate_59
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_59 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_59 row)))
  --             rewrite [neg_involutive] at hgate_59
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_59]
  --             clear hgate_59
  --             rfl

  --     lemma gate_60_next_row_check (c: ValidCircuit P P_Prime) (hgate_60: gate_60 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 126 row 0),
  --         (4, c.get_advice_wrapped 126 row 1),
  --         (4, c.get_advice_wrapped 126 row 2),
  --         (4, c.get_advice_wrapped 126 row 3),
  --         (4, c.get_advice_wrapped 126 row 4),
  --         (4, c.get_advice_wrapped 126 row 5),
  --         (4, c.get_advice_wrapped 126 row 6),
  --         (4, c.get_advice_wrapped 126 row 7),
  --         (4, c.get_advice_wrapped 126 row 8),
  --         (4, c.get_advice_wrapped 126 row 9),
  --         (4, c.get_advice_wrapped 126 row 10),
  --         (4, c.get_advice_wrapped 126 row 11),
  --         (4, c.get_advice_wrapped 131 row 0),
  --         (4, c.get_advice_wrapped 131 row 1),
  --         (4, c.get_advice_wrapped 131 row 2),
  --         (4, c.get_advice_wrapped 131 row 3),
  --       ] =
  --       c.get_advice_wrapped 7 row 20
  --       := by
  --         unfold gate_60 at hgate_60
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_60 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_60 row)))
  --             rewrite [neg_involutive] at hgate_60
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_60]
  --             clear hgate_60
  --             rfl

  --     lemma gate_61_next_row_check (c: ValidCircuit P P_Prime) (hgate_61: gate_61 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 131 row 4),
  --         (4, c.get_advice_wrapped 131 row 5),
  --         (4, c.get_advice_wrapped 131 row 6),
  --         (4, c.get_advice_wrapped 131 row 7),
  --         (4, c.get_advice_wrapped 131 row 8),
  --         (4, c.get_advice_wrapped 131 row 9),
  --         (4, c.get_advice_wrapped 131 row 10),
  --         (4, c.get_advice_wrapped 131 row 11),
  --         (4, c.get_advice_wrapped 136 row 0),
  --         (4, c.get_advice_wrapped 136 row 1),
  --         (4, c.get_advice_wrapped 136 row 2),
  --         (4, c.get_advice_wrapped 136 row 3),
  --         (4, c.get_advice_wrapped 136 row 4),
  --         (4, c.get_advice_wrapped 136 row 5),
  --         (4, c.get_advice_wrapped 136 row 6),
  --         (4, c.get_advice_wrapped 136 row 7),
  --       ] =
  --       c.get_advice_wrapped 7 row 21
  --       := by
  --         unfold gate_61 at hgate_61
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_61 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_61 row)))
  --             rewrite [neg_involutive] at hgate_61
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_61]
  --             clear hgate_61
  --             rfl

  --     lemma gate_62_next_row_check (c: ValidCircuit P P_Prime) (hgate_62: gate_62 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 107 row 0),
  --         (4, c.get_advice_wrapped 107 row 1),
  --         (4, c.get_advice_wrapped 107 row 2),
  --         (4, c.get_advice_wrapped 107 row 3),
  --         (4, c.get_advice_wrapped 107 row 4),
  --         (4, c.get_advice_wrapped 107 row 5),
  --         (4, c.get_advice_wrapped 107 row 6),
  --         (4, c.get_advice_wrapped 107 row 7),
  --         (4, c.get_advice_wrapped 107 row 8),
  --         (4, c.get_advice_wrapped 107 row 9),
  --         (4, c.get_advice_wrapped 107 row 10),
  --         (4, c.get_advice_wrapped 107 row 11),
  --         (4, c.get_advice_wrapped 112 row 0),
  --         (4, c.get_advice_wrapped 112 row 1),
  --         (4, c.get_advice_wrapped 112 row 2),
  --         (4, c.get_advice_wrapped 112 row 3),
  --       ] =
  --       c.get_advice_wrapped 7 row 22
  --       := by
  --         unfold gate_62 at hgate_62
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_62 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_62 row)))
  --             rewrite [neg_involutive] at hgate_62
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_62]
  --             clear hgate_62
  --             rfl

  --     lemma gate_63_next_row_check (c: ValidCircuit P P_Prime) (hgate_63: gate_63 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 112 row 4),
  --         (4, c.get_advice_wrapped 112 row 5),
  --         (4, c.get_advice_wrapped 112 row 6),
  --         (4, c.get_advice_wrapped 112 row 7),
  --         (4, c.get_advice_wrapped 112 row 8),
  --         (4, c.get_advice_wrapped 112 row 9),
  --         (4, c.get_advice_wrapped 112 row 10),
  --         (4, c.get_advice_wrapped 112 row 11),
  --         (4, c.get_advice_wrapped 117 row 0),
  --         (4, c.get_advice_wrapped 117 row 1),
  --         (4, c.get_advice_wrapped 117 row 2),
  --         (4, c.get_advice_wrapped 117 row 3),
  --         (4, c.get_advice_wrapped 117 row 4),
  --         (4, c.get_advice_wrapped 117 row 5),
  --         (4, c.get_advice_wrapped 117 row 6),
  --         (4, c.get_advice_wrapped 117 row 7),
  --       ] =
  --       c.get_advice_wrapped 7 row 23
  --       := by
  --         unfold gate_63 at hgate_63
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_63 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_63 row)))
  --             rewrite [neg_involutive] at hgate_63
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_63]
  --             clear hgate_63
  --             rfl

  --     lemma gate_64_next_row_check (c: ValidCircuit P P_Prime) (hgate_64: gate_64 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 117 row 8),
  --         (4, c.get_advice_wrapped 117 row 9),
  --         (4, c.get_advice_wrapped 117 row 10),
  --         (4, c.get_advice_wrapped 117 row 11),
  --         (4, c.get_advice_wrapped 122 row 0),
  --         (4, c.get_advice_wrapped 122 row 1),
  --         (4, c.get_advice_wrapped 122 row 2),
  --         (4, c.get_advice_wrapped 122 row 3),
  --         (4, c.get_advice_wrapped 122 row 4),
  --         (4, c.get_advice_wrapped 122 row 5),
  --         (4, c.get_advice_wrapped 122 row 6),
  --         (4, c.get_advice_wrapped 122 row 7),
  --         (4, c.get_advice_wrapped 122 row 8),
  --         (4, c.get_advice_wrapped 122 row 9),
  --         (4, c.get_advice_wrapped 122 row 10),
  --         (4, c.get_advice_wrapped 122 row 11),
  --       ] =
  --       c.get_advice_wrapped 8 row 12
  --       := by
  --         unfold gate_64 at hgate_64
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_64 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_64 row)))
  --             rewrite [neg_involutive] at hgate_64
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_64]
  --             clear hgate_64
  --             rfl

  --     lemma gate_65_next_row_check (c: ValidCircuit P P_Prime) (hgate_65: gate_65 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 127 row 0),
  --         (4, c.get_advice_wrapped 127 row 1),
  --         (4, c.get_advice_wrapped 127 row 2),
  --         (4, c.get_advice_wrapped 127 row 3),
  --         (4, c.get_advice_wrapped 127 row 4),
  --         (4, c.get_advice_wrapped 127 row 5),
  --         (4, c.get_advice_wrapped 127 row 6),
  --         (4, c.get_advice_wrapped 127 row 7),
  --         (4, c.get_advice_wrapped 127 row 8),
  --         (4, c.get_advice_wrapped 127 row 9),
  --         (4, c.get_advice_wrapped 127 row 10),
  --         (4, c.get_advice_wrapped 127 row 11),
  --         (4, c.get_advice_wrapped 132 row 0),
  --         (4, c.get_advice_wrapped 132 row 1),
  --         (4, c.get_advice_wrapped 132 row 2),
  --         (4, c.get_advice_wrapped 132 row 3),
  --       ] =
  --       c.get_advice_wrapped 8 row 13
  --       := by
  --         unfold gate_65 at hgate_65
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_65 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_65 row)))
  --             rewrite [neg_involutive] at hgate_65
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_65]
  --             clear hgate_65
  --             rfl

  --     lemma gate_66_next_row_check (c: ValidCircuit P P_Prime) (hgate_66: gate_66 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 132 row 4),
  --         (4, c.get_advice_wrapped 132 row 5),
  --         (4, c.get_advice_wrapped 132 row 6),
  --         (4, c.get_advice_wrapped 132 row 7),
  --         (4, c.get_advice_wrapped 132 row 8),
  --         (4, c.get_advice_wrapped 132 row 9),
  --         (4, c.get_advice_wrapped 132 row 10),
  --         (4, c.get_advice_wrapped 132 row 11),
  --         (4, c.get_advice_wrapped 137 row 0),
  --         (4, c.get_advice_wrapped 137 row 1),
  --         (4, c.get_advice_wrapped 137 row 2),
  --         (4, c.get_advice_wrapped 137 row 3),
  --         (4, c.get_advice_wrapped 137 row 4),
  --         (4, c.get_advice_wrapped 137 row 5),
  --         (4, c.get_advice_wrapped 137 row 6),
  --         (4, c.get_advice_wrapped 137 row 7),
  --       ] =
  --       c.get_advice_wrapped 8 row 14
  --       := by
  --         unfold gate_66 at hgate_66
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_66 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_66 row)))
  --             rewrite [neg_involutive] at hgate_66
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_66]
  --             clear hgate_66
  --             rfl

  --     lemma gate_67_next_row_check (c: ValidCircuit P P_Prime) (hgate_67: gate_67 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 108 row 0),
  --         (4, c.get_advice_wrapped 108 row 1),
  --         (4, c.get_advice_wrapped 108 row 2),
  --         (4, c.get_advice_wrapped 108 row 3),
  --         (4, c.get_advice_wrapped 108 row 4),
  --         (4, c.get_advice_wrapped 108 row 5),
  --         (4, c.get_advice_wrapped 108 row 6),
  --         (4, c.get_advice_wrapped 108 row 7),
  --         (4, c.get_advice_wrapped 108 row 8),
  --         (4, c.get_advice_wrapped 108 row 9),
  --         (4, c.get_advice_wrapped 108 row 10),
  --         (4, c.get_advice_wrapped 108 row 11),
  --         (4, c.get_advice_wrapped 113 row 0),
  --         (4, c.get_advice_wrapped 113 row 1),
  --         (4, c.get_advice_wrapped 113 row 2),
  --         (4, c.get_advice_wrapped 113 row 3),
  --       ] =
  --       c.get_advice_wrapped 8 row 15
  --       := by
  --         unfold gate_67 at hgate_67
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_67 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_67 row)))
  --             rewrite [neg_involutive] at hgate_67
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_67]
  --             clear hgate_67
  --             rfl

  --     lemma gate_68_next_row_check (c: ValidCircuit P P_Prime) (hgate_68: gate_68 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 113 row 4),
  --         (4, c.get_advice_wrapped 113 row 5),
  --         (4, c.get_advice_wrapped 113 row 6),
  --         (4, c.get_advice_wrapped 113 row 7),
  --         (4, c.get_advice_wrapped 113 row 8),
  --         (4, c.get_advice_wrapped 113 row 9),
  --         (4, c.get_advice_wrapped 113 row 10),
  --         (4, c.get_advice_wrapped 113 row 11),
  --         (4, c.get_advice_wrapped 118 row 0),
  --         (4, c.get_advice_wrapped 118 row 1),
  --         (4, c.get_advice_wrapped 118 row 2),
  --         (4, c.get_advice_wrapped 118 row 3),
  --         (4, c.get_advice_wrapped 118 row 4),
  --         (4, c.get_advice_wrapped 118 row 5),
  --         (4, c.get_advice_wrapped 118 row 6),
  --         (4, c.get_advice_wrapped 118 row 7),
  --       ] =
  --       c.get_advice_wrapped 8 row 16
  --       := by
  --         unfold gate_68 at hgate_68
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_68 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_68 row)))
  --             rewrite [neg_involutive] at hgate_68
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_68]
  --             clear hgate_68
  --             rfl

  --     lemma gate_69_next_row_check (c: ValidCircuit P P_Prime) (hgate_69: gate_69 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 118 row 8),
  --         (4, c.get_advice_wrapped 118 row 9),
  --         (4, c.get_advice_wrapped 118 row 10),
  --         (4, c.get_advice_wrapped 118 row 11),
  --         (4, c.get_advice_wrapped 123 row 0),
  --         (4, c.get_advice_wrapped 123 row 1),
  --         (4, c.get_advice_wrapped 123 row 2),
  --         (4, c.get_advice_wrapped 123 row 3),
  --         (4, c.get_advice_wrapped 123 row 4),
  --         (4, c.get_advice_wrapped 123 row 5),
  --         (4, c.get_advice_wrapped 123 row 6),
  --         (4, c.get_advice_wrapped 123 row 7),
  --         (4, c.get_advice_wrapped 123 row 8),
  --         (4, c.get_advice_wrapped 123 row 9),
  --         (4, c.get_advice_wrapped 123 row 10),
  --         (4, c.get_advice_wrapped 123 row 11),
  --       ] =
  --       c.get_advice_wrapped 8 row 17
  --       := by
  --         unfold gate_69 at hgate_69
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_69 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_69 row)))
  --             rewrite [neg_involutive] at hgate_69
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_69]
  --             clear hgate_69
  --             rfl

  --     lemma gate_70_next_row_check (c: ValidCircuit P P_Prime) (hgate_70: gate_70 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 128 row 0),
  --         (4, c.get_advice_wrapped 128 row 1),
  --         (4, c.get_advice_wrapped 128 row 2),
  --         (4, c.get_advice_wrapped 128 row 3),
  --         (4, c.get_advice_wrapped 128 row 4),
  --         (4, c.get_advice_wrapped 128 row 5),
  --         (4, c.get_advice_wrapped 128 row 6),
  --         (4, c.get_advice_wrapped 128 row 7),
  --         (4, c.get_advice_wrapped 128 row 8),
  --         (4, c.get_advice_wrapped 128 row 9),
  --         (4, c.get_advice_wrapped 128 row 10),
  --         (4, c.get_advice_wrapped 128 row 11),
  --         (4, c.get_advice_wrapped 133 row 0),
  --         (4, c.get_advice_wrapped 133 row 1),
  --         (4, c.get_advice_wrapped 133 row 2),
  --         (4, c.get_advice_wrapped 133 row 3),
  --       ] =
  --       c.get_advice_wrapped 8 row 18
  --       := by
  --         unfold gate_70 at hgate_70
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_70 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_70 row)))
  --             rewrite [neg_involutive] at hgate_70
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_70]
  --             clear hgate_70
  --             rfl

  --     lemma gate_71_next_row_check (c: ValidCircuit P P_Prime) (hgate_71: gate_71 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 133 row 4),
  --         (4, c.get_advice_wrapped 133 row 5),
  --         (4, c.get_advice_wrapped 133 row 6),
  --         (4, c.get_advice_wrapped 133 row 7),
  --         (4, c.get_advice_wrapped 133 row 8),
  --         (4, c.get_advice_wrapped 133 row 9),
  --         (4, c.get_advice_wrapped 133 row 10),
  --         (4, c.get_advice_wrapped 133 row 11),
  --         (4, c.get_advice_wrapped 138 row 0),
  --         (4, c.get_advice_wrapped 138 row 1),
  --         (4, c.get_advice_wrapped 138 row 2),
  --         (4, c.get_advice_wrapped 138 row 3),
  --         (4, c.get_advice_wrapped 138 row 4),
  --         (4, c.get_advice_wrapped 138 row 5),
  --         (4, c.get_advice_wrapped 138 row 6),
  --         (4, c.get_advice_wrapped 138 row 7),
  --       ] =
  --       c.get_advice_wrapped 8 row 19
  --       := by
  --         unfold gate_71 at hgate_71
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_71 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_71 row)))
  --             rewrite [neg_involutive] at hgate_71
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_71]
  --             clear hgate_71
  --             rfl

  --     lemma gate_72_next_row_check (c: ValidCircuit P P_Prime) (hgate_72: gate_72 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 109 row 0),
  --         (4, c.get_advice_wrapped 109 row 1),
  --         (4, c.get_advice_wrapped 109 row 2),
  --         (4, c.get_advice_wrapped 109 row 3),
  --         (4, c.get_advice_wrapped 109 row 4),
  --         (4, c.get_advice_wrapped 109 row 5),
  --         (4, c.get_advice_wrapped 109 row 6),
  --         (4, c.get_advice_wrapped 109 row 7),
  --         (4, c.get_advice_wrapped 109 row 8),
  --         (4, c.get_advice_wrapped 109 row 9),
  --         (4, c.get_advice_wrapped 109 row 10),
  --         (4, c.get_advice_wrapped 109 row 11),
  --         (4, c.get_advice_wrapped 114 row 0),
  --         (4, c.get_advice_wrapped 114 row 1),
  --         (4, c.get_advice_wrapped 114 row 2),
  --         (4, c.get_advice_wrapped 114 row 3),
  --       ] =
  --       c.get_advice_wrapped 8 row 20
  --       := by
  --         unfold gate_72 at hgate_72
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_72 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_72 row)))
  --             rewrite [neg_involutive] at hgate_72
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_72]
  --             clear hgate_72
  --             rfl

  --     lemma gate_73_next_row_check (c: ValidCircuit P P_Prime) (hgate_73: gate_73 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 114 row 4),
  --         (4, c.get_advice_wrapped 114 row 5),
  --         (4, c.get_advice_wrapped 114 row 6),
  --         (4, c.get_advice_wrapped 114 row 7),
  --         (4, c.get_advice_wrapped 114 row 8),
  --         (4, c.get_advice_wrapped 114 row 9),
  --         (4, c.get_advice_wrapped 114 row 10),
  --         (4, c.get_advice_wrapped 114 row 11),
  --         (4, c.get_advice_wrapped 119 row 0),
  --         (4, c.get_advice_wrapped 119 row 1),
  --         (4, c.get_advice_wrapped 119 row 2),
  --         (4, c.get_advice_wrapped 119 row 3),
  --         (4, c.get_advice_wrapped 119 row 4),
  --         (4, c.get_advice_wrapped 119 row 5),
  --         (4, c.get_advice_wrapped 119 row 6),
  --         (4, c.get_advice_wrapped 119 row 7),
  --       ] =
  --       c.get_advice_wrapped 8 row 21
  --       := by
  --         unfold gate_73 at hgate_73
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_73 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_73 row)))
  --             rewrite [neg_involutive] at hgate_73
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_73]
  --             clear hgate_73
  --             rfl

  --     lemma gate_74_next_row_check (c: ValidCircuit P P_Prime) (hgate_74: gate_74 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 119 row 8),
  --         (4, c.get_advice_wrapped 119 row 9),
  --         (4, c.get_advice_wrapped 119 row 10),
  --         (4, c.get_advice_wrapped 119 row 11),
  --         (4, c.get_advice_wrapped 124 row 0),
  --         (4, c.get_advice_wrapped 124 row 1),
  --         (4, c.get_advice_wrapped 124 row 2),
  --         (4, c.get_advice_wrapped 124 row 3),
  --         (4, c.get_advice_wrapped 124 row 4),
  --         (4, c.get_advice_wrapped 124 row 5),
  --         (4, c.get_advice_wrapped 124 row 6),
  --         (4, c.get_advice_wrapped 124 row 7),
  --         (4, c.get_advice_wrapped 124 row 8),
  --         (4, c.get_advice_wrapped 124 row 9),
  --         (4, c.get_advice_wrapped 124 row 10),
  --         (4, c.get_advice_wrapped 124 row 11),
  --       ] =
  --       c.get_advice_wrapped 8 row 22
  --       := by
  --         unfold gate_74 at hgate_74
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_74 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_74 row)))
  --             rewrite [neg_involutive] at hgate_74
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_74]
  --             clear hgate_74
  --             rfl

  --     lemma gate_75_next_row_check (c: ValidCircuit P P_Prime) (hgate_75: gate_75 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 129 row 0),
  --         (4, c.get_advice_wrapped 129 row 1),
  --         (4, c.get_advice_wrapped 129 row 2),
  --         (4, c.get_advice_wrapped 129 row 3),
  --         (4, c.get_advice_wrapped 129 row 4),
  --         (4, c.get_advice_wrapped 129 row 5),
  --         (4, c.get_advice_wrapped 129 row 6),
  --         (4, c.get_advice_wrapped 129 row 7),
  --         (4, c.get_advice_wrapped 129 row 8),
  --         (4, c.get_advice_wrapped 129 row 9),
  --         (4, c.get_advice_wrapped 129 row 10),
  --         (4, c.get_advice_wrapped 129 row 11),
  --         (4, c.get_advice_wrapped 134 row 0),
  --         (4, c.get_advice_wrapped 134 row 1),
  --         (4, c.get_advice_wrapped 134 row 2),
  --         (4, c.get_advice_wrapped 134 row 3),
  --       ] =
  --       c.get_advice_wrapped 8 row 23
  --       := by
  --         unfold gate_75 at hgate_75
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_75 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_75 row)))
  --             rewrite [neg_involutive] at hgate_75
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_75]
  --             clear hgate_75
  --             rfl

  --     lemma gate_76_next_row_check (c: ValidCircuit P P_Prime) (hgate_76: gate_76 c): ∀ row < c.n,
  --       c.get_fixed 2 row = 0 ∨
  --       Decode.expr [
  --         (4, c.get_advice_wrapped 134 row 4),
  --         (4, c.get_advice_wrapped 134 row 5),
  --         (4, c.get_advice_wrapped 134 row 6),
  --         (4, c.get_advice_wrapped 134 row 7),
  --         (4, c.get_advice_wrapped 134 row 8),
  --         (4, c.get_advice_wrapped 134 row 9),
  --         (4, c.get_advice_wrapped 134 row 10),
  --         (4, c.get_advice_wrapped 134 row 11),
  --         (4, c.get_advice_wrapped 139 row 0),
  --         (4, c.get_advice_wrapped 139 row 1),
  --         (4, c.get_advice_wrapped 139 row 2),
  --         (4, c.get_advice_wrapped 139 row 3),
  --         (4, c.get_advice_wrapped 139 row 4),
  --         (4, c.get_advice_wrapped 139 row 5),
  --         (4, c.get_advice_wrapped 139 row 6),
  --         (4, c.get_advice_wrapped 139 row 7),
  --       ] =
  --       c.get_advice_wrapped 9 row 12
  --       := by
  --         unfold gate_76 at hgate_76
  --         intro row h_row_range
  --         cases eq_zero_or_neZero (c.get_fixed 2 row) with
  --           | inl hzero => left; assumption
  --           | inr h_non_zero =>
  --             right
  --             have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --             replace hgate_76 := eq_neg_of_add_eq_zero_left ((or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_76 row)))
  --             rewrite [neg_involutive] at hgate_76
  --             simp only [ValidCircuit.get_advice_wrapped, add_zero, Nat.mod_eq_of_lt h_row_range]
  --             unfold Decode.expr
  --             simp only [BIT_COUNT, List.foldr_nil, List.foldr_cons, Nat.reduceMul, zmod_2pow12, zmod_2pow18, mul_comm]
  --             simp only [mul_comm (0: ZMod P)]
  --             rewrite [hgate_76]
  --             clear hgate_76
  --             rfl
  --   end NextRowCheck

  --   section AbsorbVerifyInput
  --     -- lemma gate_78_absorb_verify_input (c: ValidCircuit P P_Prime) (hgate_78: gate_78 c): ∀ row < c.n,
  --     --   c.get_fixed 3 row = 0 ∨
  --     --   row > 312 ∨
  --     --   (row = 0) =
  --     --   c.get_advice_wrapped 9 row 12
  --     --   := by
  --     --     unfold gate_78 at hgate_78
  --     --     intro row h_row_range
  --     --     cases eq_zero_or_neZero (c.get_fixed 3 row) with
  --     --       | inl hzero => left; assumption
  --     --       | inr h_non_zero =>
  --     --         right
  --     --         have no_zero_div := no_zero_divisors_zmod_p P_Prime
  --     --         replace hgate_78 := (or_iff_right (h_non_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (hgate_78 row))
  --     --         replace hgate_78 := eq_zero_or_eq_zero_of_mul_eq_zero hgate_78
  --     --         cases hgate_78 with
  --     --           | inl hgate_78 =>
  --     --             replace hgate_78 := eq_neg_of_add_eq_zero_left hgate_78
  --     --             rewrite [neg_involutive] at hgate_78




  --   end AbsorbVerifyInput
  -- end Gates

end Keccak

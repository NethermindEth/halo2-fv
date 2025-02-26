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

  namespace Decode
    def expr (parts: List (ℕ × ZMod P)) : ZMod P :=
      List.foldr
        (λ (part: ℕ × ZMod P) (acc: ZMod P) => 2^(BIT_COUNT*part.1) * acc + part.2)
        0
        parts
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

  namespace ComposeRlc
    def expr (expressions: List (ZMod P)) (r: ZMod P): ZMod P :=
      (expressions.foldl (λ (rlc, mult) (expr) => (rlc + expr * mult, mult*r)) (0, 1)).1
  end ComposeRlc

  def is_final (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 0 row
  def length (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 2 row
  def data_rlc (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 1 row
  def hash_rlc (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 3 row

  def start_new_hash (c: ValidCircuit P P_Prime) (row: ℕ): Prop := c.get_fixed 1 row = 1 ∨ is_final c row = 1
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
  -- packed_parts: gate_2
  def input_bytes (c: ValidCircuit P P_Prime) (round: ℕ) :=
    Transform.split_expr c round
      (cell_offset := 64) -- TODO check
      (rot := 0)
      (target_part_size := NUM_BYTES_PER_WORD)
      (transform_offset := 8) -- TODO check

  -- Padding data (line 230)
  def is_paddings (c: ValidCircuit P P_Prime) (round: ℕ): (Fin 8) → ZMod P
    | 0 => cell_manager c round 84
    | 1 => cell_manager c round 85
    | 2 => cell_manager c round 86
    | 3 => cell_manager c round 87
    | 4 => cell_manager c round 88
    | 5 => cell_manager c round 89
    | 6 => cell_manager c round 90
    | 7 => cell_manager c round 91

  --Theta (line 241)
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

  -- Rho/Pi
  def rho_by_pi_num_word_parts := (target_part_sizes_rot get_num_bits_per_base_chi_lookup 0).length
  instance : NeZero rho_by_pi_num_word_parts where
    out := by
      unfold rho_by_pi_num_word_parts target_part_sizes_rot get_num_bits_per_base_chi_lookup CHI_BASE_LOOKUP_RANGE RHO_PI_LOOKUP_RANGE
      simp only [Nat.reduceLeDiff, max_eq_left, tsub_zero, List.length_join, List.map_map, Nat.sum_eq_listSum, ne_eq]
      unfold get_num_bits_per_lookup
      have h: Nat.log 5 (2^KECCAK_DEGREE - keccak_unusable_rows) = 4 := by
        rewrite [Nat.log_eq_iff] <;> decide
      rewrite [h]
      decide
  def rho_pi_chi_cells (c: ValidCircuit P P_Prime) (round: ℕ) (p: Fin 3) (i j: Fin 5) (idx: Fin rho_by_pi_num_word_parts): ZMod P :=
    -- let row_idx: ℕ := ↑idx + ↑j * rho_by_pi_num_word_parts + ↑p * 5 * rho_by_pi_num_word_parts
    -- cell_manager c round (
    --   336 + --start
    --   DEFAULT_KECCAK_ROWS*↑i +
    --   row_idx % DEFAULT_KECCAK_ROWS +
    --   5 * (row_idx / DEFAULT_KECCAK_ROWS) * DEFAULT_KECCAK_ROWS
    -- )
    let row_idx: ℕ := (↑idx + ↑j * rho_by_pi_num_word_parts) % DEFAULT_KECCAK_ROWS
    let col_idx: ℕ := (↑idx + ↑j * rho_by_pi_num_word_parts) / DEFAULT_KECCAK_ROWS
    let cols_per_p: ℕ := 5 * ((rho_by_pi_num_word_parts * 5 + DEFAULT_KECCAK_ROWS - 1) / DEFAULT_KECCAK_ROWS)
    cell_manager c round (
      336 -- start
      + p * cols_per_p * DEFAULT_KECCAK_ROWS
      + row_idx
      + i * DEFAULT_KECCAK_ROWS
      + col_idx * DEFAULT_KECCAK_ROWS * 5
    )



  -- 1240 =
  -- 336 + 904 =
  -- 336 + 75*12 + 4
  -- row_idx%12 = 4
  -- 12i + 5*(row_idx-4) = 75
  -- i = 0
  -- row+idx = 18
  -- idx + j * 16 + p * 5 * 16 = 18
  -- p = 0
  -- idx = 2
  -- j = 1
  -- rho_pi_chi_cells
  -- Chi







  -- 336 - start
  -- p = 0
  --   start_region - at multiple of 12
  --   row_idx = 0
  --   j = 0
  --     _ = 0
  --       for i = 0..5 rho_pi_chi_cells[0][i][0][0] = cell manager start + DEFAULT_KECCAK_ROWS*i
  --       row_idx += 1
  --






  --    | 28                                      | 29                     | 30                     | 31                     | 32                      |
  -- 0  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 0] |[p=0][i=1][j=0][idx= 0] |[p=0][i=2][j=0][idx= 0] |[p=0][i=3][j=0][idx= 0] | [p=0][i=4][j=0][idx= 0] |
  -- 1  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 1] |[p=0][i=1][j=0][idx= 1] |[p=0][i=2][j=0][idx= 1] |[p=0][i=3][j=0][idx= 1] | [p=0][i=4][j=0][idx= 1] |
  -- 2  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 2] |[p=0][i=1][j=0][idx= 2] |[p=0][i=2][j=0][idx= 2] |[p=0][i=3][j=0][idx= 2] | [p=0][i=4][j=0][idx= 2] |
  -- 3  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 3] |[p=0][i=1][j=0][idx= 3] |[p=0][i=2][j=0][idx= 3] |[p=0][i=3][j=0][idx= 3] | [p=0][i=4][j=0][idx= 3] |
  -- 4  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 4] |[p=0][i=1][j=0][idx= 4] |[p=0][i=2][j=0][idx= 4] |[p=0][i=3][j=0][idx= 4] | [p=0][i=4][j=0][idx= 4] |
  -- 5  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 5] |[p=0][i=1][j=0][idx= 5] |[p=0][i=2][j=0][idx= 5] |[p=0][i=3][j=0][idx= 5] | [p=0][i=4][j=0][idx= 5] |
  -- 6  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 6] |[p=0][i=1][j=0][idx= 6] |[p=0][i=2][j=0][idx= 6] |[p=0][i=3][j=0][idx= 6] | [p=0][i=4][j=0][idx= 6] |
  -- 7  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 7] |[p=0][i=1][j=0][idx= 7] |[p=0][i=2][j=0][idx= 7] |[p=0][i=3][j=0][idx= 7] | [p=0][i=4][j=0][idx= 7] |
  -- 8  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 8] |[p=0][i=1][j=0][idx= 8] |[p=0][i=2][j=0][idx= 8] |[p=0][i=3][j=0][idx= 8] | [p=0][i=4][j=0][idx= 8] |
  -- 9  | rho_pi_chi_cells[p=0][i=0][j=0][idx= 9] |[p=0][i=1][j=0][idx= 9] |[p=0][i=2][j=0][idx= 9] |[p=0][i=3][j=0][idx= 9] | [p=0][i=4][j=0][idx= 9] |
  -- 10 | rho_pi_chi_cells[p=0][i=0][j=0][idx=10] |[p=0][i=1][j=0][idx=10] |[p=0][i=2][j=0][idx=10] |[p=0][i=3][j=0][idx=10] | [p=0][i=4][j=0][idx=10] |
  -- 11 | rho_pi_chi_cells[p=0][i=0][j=0][idx=11] |[p=0][i=1][j=0][idx=11] |[p=0][i=2][j=0][idx=11] |[p=0][i=3][j=0][idx=11] | [p=0][i=4][j=0][idx=11] |

  def os' (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5) :=
    Decode.expr (
      (List.range rho_by_pi_num_word_parts).map
      (λ idx: ℕ => (get_num_bits_per_base_chi_lookup, rho_pi_chi_cells c round 2 x y idx))
    )

  -- iota (line 438)

  def iota_s (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5) :=
    match x, y with
      | 0, 0 => Decode.expr (
        Transform.split_expr c round
          (cell_offset := 1632)
          (rot := 0)
          (target_part_size := get_num_bits_per_absorb_lookup)
          (transform_offset := 12) -- TODO
      )
      | _, _ => os' c round x y


  -- Squeeze data (line 470)
  def squeeze_from (c: ValidCircuit P P_Prime) (round: ℕ):= cell_manager c round 1656

  -- Squeeze (line 477)
  def squeeze_bytes (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) := Transform.split_expr c round
    (cell_offset := 1657) -- TODO
    (rot := 0)
    (target_part_size := 8)
    (transform_offset := 23)

  -- Absorb (line 512)
  def continue_hash (c: ValidCircuit P P_Prime) (row: ℕ) : Prop := ¬start_new_hash c row

  -- Collect the bytes that are spread out over previous rows (line 550)
  def hash_bytes (c: ValidCircuit P P_Prime) (round: ℕ) :=
    (
      squeeze_bytes c (round-1) ++
      squeeze_bytes c (round-2) ++
      squeeze_bytes c (round-3) ++
      squeeze_bytes c (round-4)
    ).map (λ (_, val) => val)

  def hash_bytes_le (c: ValidCircuit P P_Prime) (round: ℕ) := (hash_bytes c round).reverse

  def hash_words (c: ValidCircuit P P_Prime) (round: ℕ): (Fin 4) → ZMod P
    | 0 => s c round 0 0
    | 1 => s c round 1 0
    | 2 => s c round 2 0
    | 3 => s c round 3 0

  -- Some general input checks (line 592)
  def boolean_is_final (c: ValidCircuit P P_Prime): Prop :=
    ∀ round ≤ 25, is_final c (12*round) = 0 ∨ is_final c (12*round) = 1

  -- Enforce fixed values on the first row (line 602)
  def is_final_disabled_on_first_row (c: ValidCircuit P P_Prime): Prop :=
    is_final c 0 = 0

  -- Enforce logic for when this block is the last block for a hash (line 612)
  def last_is_padding_in_block (c: ValidCircuit P P_Prime) (round: ℕ) :=
    is_paddings c (round - (NUM_ROUNDS + 1 - NUM_WORDS_TO_ABSORB))

  def is_padding_prev (c: ValidCircuit P P_Prime) (round: ℕ): (Fin 8) → ZMod P
    | 0 => is_paddings c (round-1) 7
    | x => is_paddings c round (x-1)

  def is_first_padding (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 8): ZMod P :=
    is_paddings c round idx - is_padding_prev c round idx
end Keccak

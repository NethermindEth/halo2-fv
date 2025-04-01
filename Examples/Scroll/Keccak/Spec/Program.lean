import Examples.Scroll.Keccak.Extraction
import Examples.Scroll.Keccak.Lookups.ChiBase.Lookups
import Examples.Scroll.Keccak.Lookups.Normalize_3.Lookups
import Examples.Scroll.Keccak.Lookups.Normalize_4.Lookups
import Examples.Scroll.Keccak.Lookups.Normalize_6.Lookups
import Examples.Scroll.Keccak.Lookups.PackTable.Lookups
import Examples.Scroll.Keccak.Lookups.PackTable.Packed
import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.Util
import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Selectors
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Examples.Util

namespace Keccak

  def get_num_rows_per_round: ℕ :=
    Env.KECCAK_ROWS.getD DEFAULT_KECCAK_ROWS

  def keccak_unusable_rows: ℕ :=
    let UNUSABLE_ROWS_BY_KECCAK_ROWS := [
      53, 67, 63, 59, 45, 79, 77, 75, 73, 71, 69, 67, 65, 63, 61, 59, 57, 71, 89, 107, 107, 107,
      107, 107,
    ]
    UNUSABLE_ROWS_BY_KECCAK_ROWS[get_num_rows_per_round - NUM_BYTES_PER_WORD -1]?.getD 107

  def get_degree: ℕ :=
    Env.KECCAK_DEGREE.getD 19

  def get_num_bits_per_lookup (range: ℕ): ℕ :=
    Nat.log range (2^get_degree - keccak_unusable_rows)

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
    def expr_res (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ): List (ℕ × ZMod P) :=
      (WordParts.new target_part_size rot false
      ).zipIdx.map (
        λ (bits, offset) => (bits.length, cell_manager c round (cell_offset + offset))
      )

    def constraint (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ) (input: ZMod P): Prop :=
      Decode.expr (expr_res c cell_offset round rot target_part_size) = input

    def expr (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ) (input: ZMod P): List (ℕ × ZMod P) × Prop :=
      (
        Split.expr_res c cell_offset round rot target_part_size,
        Split.constraint c cell_offset round rot target_part_size input
      )
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

    def expr_res [NeZero K] (output_cells: Fin K → ZMod P) (target_part_size: ℕ):=
      output_parts
        (output_cells := (List.range K).map (λ x: ℕ => output_cells (Fin.ofNat' K x)))
        (target_sizes := target_part_sizes target_part_size)

    def expr [NeZero K] (c: ValidCircuit P P_Prime) (output_cells: Fin K → ZMod P) (cell_offset round: ℕ) (input: ZMod P) (rot target_part_size: ℕ) :=
      (
        expr_res output_cells target_part_size,
        constraint c output_cells cell_offset round input rot target_part_size
      )
  end SplitUniform

  namespace TransformTo
    def expr
      (cells: List (ZMod P))
      (input: List (ℕ × ZMod P))
      (transform_table: ℕ → (ZMod P × ZMod P))
    : List (ℕ × ZMod P) × Prop :=
      (
        (input.zip cells).map (λ ⟨⟨n, _⟩, x⟩ => (n, x)),
        cells.length ≥ input.length ∧
        ∀ pair ∈ input.zip cells, ∃ lookup_row, transform_table lookup_row = (pair.1.2, pair.2)
      )

  end TransformTo

  namespace Transform
    def split_expr
      (c: ValidCircuit P P_Prime)
      (cell_offset round rot target_part_size transform_offset: ℕ)
      (input: List (ℕ × ZMod P))
      (split_input: ZMod P)
      (transform_table: ℕ → (ZMod P × ZMod P))
      (uniform_lookup: Bool)
    : List (ℕ × ZMod P) × Prop :=
      let res := Split.expr_res c (cell_offset + transform_offset) round rot target_part_size
      (
        res,
        (input, True) = Split.expr c cell_offset round rot target_part_size split_input ∧
        (uniform_lookup = true → get_num_rows_per_round ∣ transform_offset) ∧
        (∀ cell ∈ input.zip res, ∃ lookup_row, transform_table lookup_row = (cell.1.2, cell.2.2))
      )

    def split_expr_old (c: ValidCircuit P P_Prime) (cell_offset round rot target_part_size: ℕ) (transform_offset: ℕ): List (ℕ × ZMod P) :=
      Split.expr_res c (cell_offset + transform_offset) round rot target_part_size
  end Transform

  namespace ComposeRlc
    def expr (expressions: List (ZMod P)) (r: ZMod P): ZMod P :=
      (expressions.foldl (λ (rlc, mult) (expr) => (rlc + expr * mult, mult*r)) (0, 1)).1
  end ComposeRlc

  namespace Scatter
    def expr (value count: ℕ): ZMod P :=
      Lookups.PackTable.pack P (List.replicate count value)
  end Scatter

  def is_final (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 0 row
  def length (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 2 row
  def data_rlc (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 1 row
  def hash_rlc (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_advice 3 row

  def start_new_hash (c: ValidCircuit P P_Prime) (row: ℕ): Prop := c.get_fixed 1 row = 1 ∨ is_final c row = 1
  def round_cst (c: ValidCircuit P P_Prime) (row: ℕ): ZMod P := c.get_fixed 7 row

  def s (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5): ZMod P :=
    cell_manager c round ((5*↑x) + ↑y)
  -- def s_next

  -- Absorb data (line 148)
  def absorb_from (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := cell_manager c round 25
  def absorb_data (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := cell_manager c round 26
  def absorb_result (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := cell_manager c round 27 -- bound by gate 1

  -- def absorb_from_next
  -- def absorb_data_next
  -- def absorb_result_next

  -- Absorb (line 165)
  def input (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P := absorb_from c round + absorb_data c round -- bound by gate 0
  def absorb_fat (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Split.expr c round
      (cell_offset := 36)
      (rot := 0)
      (target_part_size := get_num_bits_per_absorb_lookup)
      (input := input c round)

  def absorb_res (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Transform.split_expr c round
      (cell_offset := 36)
      (rot := 0)
      (target_part_size := get_num_bits_per_absorb_lookup)
      (transform_offset := 12)
      (input := (absorb_fat c round).1)
      (split_input := input c round)
      (transform_table := Lookups.Normalize_3.transform_table P)
      (uniform_lookup := true)

  def require_equal_absorb_result (c: ValidCircuit P P_Prime) (round: ℕ) : Prop :=
    Decode.expr (absorb_res c round).1 = absorb_result c round

  --Process inputs (line 198)
  def packed_parts (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Split.expr c round
      (cell_offset := 60)
      (rot := 0)
      (target_part_size := NUM_BYTES_PER_WORD)
      (input := absorb_data c round)

  def input_bytes (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Transform.split_expr c round
      (cell_offset := 60)
      (rot := 0)
      (target_part_size := NUM_BYTES_PER_WORD)
      (transform_offset := 12)
      (input := (packed_parts c round).1)
      (split_input := absorb_data c round)
      (transform_table := Lookups.PackTable.transform_table P)
      (uniform_lookup := true)

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
  def part_size_c := get_num_bits_per_theta_c_lookup
  def c_parts (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 5) : List (ℕ × ZMod P) × Prop :=
    Split.expr c round
      (cell_offset := 96 + 22*↑idx)
      (rot := 1)
      (target_part_size := part_size_c)
      (input := s c round idx 0 + s c round idx 1 + s c round idx 2 + s c round idx 3 + s c round idx 4)

  def bc (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 5): List (ℕ × ZMod P) × Prop :=
    Transform.split_expr c round
      (cell_offset := 96 + 22*↑idx)
      (rot := 1)
      (target_part_size := part_size_c)
      (transform_offset := 120)
      (input := (c_parts c round idx).1)
      (split_input := s c round idx 0 + s c round idx 1 + s c round idx 2 + s c round idx 3 + s c round idx 4)
      (transform_table := Lookups.Normalize_6.transform_table P)
      (uniform_lookup := true)

  def t (c: ValidCircuit P P_Prime) (round: ℕ) (x: Fin 5) :=
    (Decode.expr (bc c round (x + 4)).1 + Decode.expr ((bc c round (x+1)).1.rotateRight (get_rotate_count 1 part_size_c)))

  def os (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5) :=
    s c round x y + t c round x

  -- Rho/Pi (line 299)
  def rho_by_pi_part_size := get_num_bits_per_base_chi_lookup
  def rho_by_pi_target_word_sizes := target_part_sizes rho_by_pi_part_size
  def rho_by_pi_num_word_parts := rho_by_pi_target_word_sizes.length
  instance : NeZero rho_by_pi_num_word_parts where
    out := by
      unfold rho_by_pi_num_word_parts rho_by_pi_target_word_sizes target_part_sizes rho_by_pi_part_size get_num_bits_per_base_chi_lookup CHI_BASE_LOOKUP_RANGE RHO_PI_LOOKUP_RANGE
      simp [keccak_constants]
      unfold get_num_bits_per_lookup
      have h: Nat.log 5 (2^get_degree - keccak_unusable_rows) = 4 := by
        rewrite [Nat.log_eq_iff] <;> decide
      rewrite [h]
      decide
  def rho_pi_chi_cells (c: ValidCircuit P P_Prime) (round: ℕ) (p: Fin 3) (i j: Fin 5) (idx: Fin rho_by_pi_num_word_parts): ZMod P :=
    let row_idx: ℕ := (↑idx + ↑j * rho_by_pi_num_word_parts) % get_num_rows_per_round
    let col_idx: ℕ := (↑idx + ↑j * rho_by_pi_num_word_parts) / get_num_rows_per_round
    let cols_per_p: ℕ := 5 * ((rho_by_pi_num_word_parts * 5 + get_num_rows_per_round - 1) / get_num_rows_per_round)
    cell_manager c round (
      336 -- start
      + p * cols_per_p * get_num_rows_per_round
      + row_idx
      + i * get_num_rows_per_round
      + col_idx * get_num_rows_per_round * 5
    )
  def rho_pi_chi_column (p: Fin 3) (i j: Fin 5) (idx: Fin rho_by_pi_num_word_parts) :=
    (
      35 +
      ↑p * (5 * ((rho_by_pi_num_word_parts * 5 + get_num_rows_per_round - 1) / get_num_rows_per_round)) +
      ↑i +
      (↑idx + ↑j * rho_by_pi_num_word_parts) / get_num_rows_per_round * 5
    )

  def rho_pi_chi_row (c: ValidCircuit P P_Prime) (round: ℕ) (j: Fin 5) (idx: Fin rho_by_pi_num_word_parts) :=
    ((12 * round + ((↑idx + ↑j * rho_by_pi_num_word_parts) % get_num_rows_per_round)) % c.n)

  def num_rho_pi_chi_columns := 6

  def rho_pi_chi_column_starts (p: Fin 3) := rho_pi_chi_column p 0 0 0

  -- Do the transformation, resulting in the word parts also being normalized (line 342)
  def pi_region_start := 1596

  def s_parts_cell_offsets (i j: Fin 5): ℕ :=
    match i, j with
      | 0, 0 => pi_region_start
      | 1, 0 => pi_region_start
      | 2, 0 => pi_region_start + 2
      | 3, 0 => pi_region_start + 4
      | 4, 0 => pi_region_start + 4
      | 0, 1 => pi_region_start + 4
      | 1, 1 => pi_region_start + 4
      | 2, 1 => pi_region_start + 6
      | 3, 1 => pi_region_start + 8
      | 4, 1 => pi_region_start + 10
      | 0, 2 => pi_region_start + 10
      | 1, 2 => pi_region_start + 12
      | 2, 2 => pi_region_start + 14
      | 3, 2 => pi_region_start + 16
      | 4, 2 => pi_region_start + 18
      | 0, 3 => pi_region_start + 20
      | 1, 3 => pi_region_start + 22
      | 2, 3 => pi_region_start + 24
      | 3, 3 => pi_region_start + 26
      | 4, 3 => pi_region_start + 28
      | 0, 4 => pi_region_start + 28
      | 1, 4 => pi_region_start + 30
      | 2, 4 => pi_region_start + 32
      | 3, 4 => pi_region_start + 34
      | 4, 4 => pi_region_start + 34

  def pi_region_end := 1632

  def s_parts (c: ValidCircuit P P_Prime) (round: ℕ) (i j: Fin 5): List (ℕ × ZMod P) × Prop :=
    SplitUniform.expr c round
      (output_cells := rho_pi_chi_cells c round 0 j (2*i + 3*j))
      (cell_offset := s_parts_cell_offsets i j)
      (input := os c round i j)
      (rot := RHO_MATRIX i j)
      (target_part_size := rho_by_pi_part_size)

  def s_parts' (c: ValidCircuit P P_Prime) (round: ℕ) (i j: Fin 5): List (ℕ × ZMod P) × Prop :=
    TransformTo.expr
      (cells := (List.range rho_by_pi_num_word_parts).map (λ x => rho_pi_chi_cells c round 1 j (2*i + 3*j) x))
      (input := (s_parts c round i j).1)
      (transform_table := Lookups.Normalize_4.transform_table P)

  def os_parts (c: ValidCircuit P P_Prime) (round: ℕ): Fin 5 → Fin 5 → List (ℕ × ZMod P)
    | 0, 0 => (s_parts' c round (i := 0) (j := 0)).1
    | 0, 1 => (s_parts' c round (i := 3) (j := 0)).1
    | 0, 2 => (s_parts' c round (i := 1) (j := 0)).1
    | 0, 3 => (s_parts' c round (i := 4) (j := 0)).1
    | 0, 4 => (s_parts' c round (i := 2) (j := 0)).1
    | 1, 0 => (s_parts' c round (i := 1) (j := 1)).1
    | 1, 1 => (s_parts' c round (i := 4) (j := 1)).1
    | 1, 2 => (s_parts' c round (i := 2) (j := 1)).1
    | 1, 3 => (s_parts' c round (i := 0) (j := 1)).1
    | 1, 4 => (s_parts' c round (i := 3) (j := 1)).1
    | 2, 0 => (s_parts' c round (i := 2) (j := 2)).1
    | 2, 1 => (s_parts' c round (i := 0) (j := 2)).1
    | 2, 2 => (s_parts' c round (i := 3) (j := 2)).1
    | 2, 3 => (s_parts' c round (i := 1) (j := 2)).1
    | 2, 4 => (s_parts' c round (i := 4) (j := 2)).1
    | 3, 0 => (s_parts' c round (i := 3) (j := 3)).1
    | 3, 1 => (s_parts' c round (i := 1) (j := 3)).1
    | 3, 2 => (s_parts' c round (i := 4) (j := 3)).1
    | 3, 3 => (s_parts' c round (i := 2) (j := 3)).1
    | 3, 4 => (s_parts' c round (i := 0) (j := 3)).1
    | 4, 0 => (s_parts' c round (i := 4) (j := 4)).1
    | 4, 1 => (s_parts' c round (i := 2) (j := 4)).1
    | 4, 2 => (s_parts' c round (i := 0) (j := 4)).1
    | 4, 3 => (s_parts' c round (i := 3) (j := 4)).1
    | 4, 4 => (s_parts' c round (i := 1) (j := 4)).1

  def os_parts_shuffle (c: ValidCircuit P P_Prime): Prop :=
    ∀ round, ∀ j i, os_parts c round j (2*i + 3*j) = (s_parts' c round (i := i) (j := j)).1

  -- Pi parts range check (line 371)
  def pi_parts_range_check (c: ValidCircuit P P_Prime)
    (idx: Finset.Ico pi_region_start pi_region_end) (row: ℕ) : Prop :=
      row < c.usable_rows → ∃ lookup_row,
        c.get_advice (cell_manager_column idx) row =
        (Lookups.Normalize_4.transform_table P lookup_row).1

  -- Chi (line 387)

  def chi_part_size_base := get_num_bits_per_base_chi_lookup

  def chi_base_input (c: ValidCircuit P P_Prime) (idx: Finset.Icc 0 num_rho_pi_chi_columns) (i: Fin 5) :=
    c.get_advice (rho_pi_chi_column_starts 1 + idx * 5 + i)
  def chi_base_output (c: ValidCircuit P P_Prime) (idx: Finset.Icc 0 num_rho_pi_chi_columns) (i: Fin 5) :=
    c.get_advice (rho_pi_chi_column_starts 2 + idx * 5 + i)
  def chi_base_input' (c: ValidCircuit P P_Prime) (idx: Finset.Icc 0 num_rho_pi_chi_columns) (i: Fin 5) (row: ℕ) :=
    (@Scatter.expr P 3 chi_part_size_base)
      - 2 * chi_base_input c idx i row
      + chi_base_input c idx (i+1) row
      - chi_base_input c idx (i+2) row

  def chi_base {P P_Prime} (c: ValidCircuit P P_Prime) (idx: Finset.Icc 0 num_rho_pi_chi_columns) (i: Fin 5) : Prop :=
    ∀ row < c.usable_rows, ∃ lookup_row,
      (chi_base_input' c idx i row, chi_base_output c idx i row) =
      Lookups.ChiBase.transform_table P lookup_row

  def os' (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5) :=
    Decode.expr (
      (List.range rho_by_pi_num_word_parts).map
      (λ idx: ℕ => (get_num_bits_per_base_chi_lookup, rho_pi_chi_cells c round 2 x y idx))
    )

  -- iota (line 438)

  def iota_part_size: ℕ := get_num_bits_per_absorb_lookup
  def iota_input (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P :=
    os' c round 0 0 + round_cst c (get_num_rows_per_round * round)

  def iota_parts (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Split.expr c round
      (cell_offset := 1632)
      (rot := 0)
      (target_part_size := iota_part_size)
      (input := iota_input c round)

  def iota_s_0_0_transform (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Transform.split_expr c round
      (cell_offset := 1632)
      (rot := 0)
      (target_part_size := iota_part_size)
      (transform_offset := 12)
      (input := (iota_parts c round).1)
      (split_input := iota_input c round)
      (transform_table := Lookups.Normalize_3.transform_table P)
      (uniform_lookup := true)

  def iota_s (c: ValidCircuit P P_Prime) (round: ℕ) (x y: Fin 5): ZMod P :=
    match x, y with
      | 0, 0 => Decode.expr (iota_s_0_0_transform c round).1
      | _, _ => os' c round x y

  def next_row_check (c: ValidCircuit P P_Prime) (round: ℕ) (i j: Fin 5): Prop :=
    iota_s c round i j = s c (round + 1) i j

  -- Squeeze data (line 470)
  def squeeze_from (c: ValidCircuit P P_Prime) (round: ℕ):= cell_manager c round 1656

  -- Squeeze (line 477)
  def squeeze_from_parts (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Split.expr c round
      (cell_offset := 1668)
      (rot := 0)
      (target_part_size := 8)
      (input := squeeze_from c round)

  def squeeze_bytes (c: ValidCircuit P P_Prime) (round: ℕ): List (ℕ × ZMod P) × Prop :=
    Transform.split_expr c round
      (cell_offset := 1668)
      (rot := 0)
      (target_part_size := 8)
      (transform_offset := 12)
      (input := (squeeze_from_parts c round).1)
      (split_input := squeeze_from c round)
      (transform_table := Lookups.PackTable.transform_table P)
      (uniform_lookup := true)

  -- Absorb (line 512)
  def continue_hash (c: ValidCircuit P P_Prime) (row: ℕ) : Prop := ¬start_new_hash c row

  def absorb_positions: List (Fin 5 × Fin 5) := [
    (0,0),
    (1,0),
    (2,0),
    (3,0),
    (4,0),
    (0,1),
    (1,1),
    (2,1),
    (3,1),
    (4,1),
    (0,2),
    (1,2),
    (2,2),
    (3,2),
    (4,2),
    (0,3),
    (1,3),
  ]

  def a_slice (i j: Fin 5) : ℕ := (i: ℕ) + 5*(j: ℕ)

  def absorb_gate (c: ValidCircuit P P_Prime) (round: ℕ) (i j: Fin 5): Prop :=
    ((i,j) ∈ absorb_positions → (
      (continue_hash c (get_num_rows_per_round * round) → (
        absorb_from c (round + a_slice i j + 1) = s c round i j ∧
        absorb_result c (round + a_slice i j + 1) = s c (round+1) i j
      )) ∧
      (¬continue_hash c (get_num_rows_per_round * round) → (
        absorb_data c (round + a_slice i j + 1) = s c (round+1) i j
      ))
    ))  ∧
    ((i,j) ∉ absorb_positions → (
      (continue_hash c (get_num_rows_per_round * round) → (
        s c round i j = s c (round+1) i j
      )) ∧
      (¬continue_hash c (get_num_rows_per_round * round) → (
        s c (round+1) i j = 0
      ))
    ))

  -- Collect the bytes that are spread out over previous rows (line 550)
  def hash_bytes (c: ValidCircuit P P_Prime) (round: ℕ): List (ZMod P) :=
    (
      (squeeze_bytes c (round-1)).1 ++
      (squeeze_bytes c (round-2)).1 ++
      (squeeze_bytes c (round-3)).1 ++
      (squeeze_bytes c (round-4)).1
    ).map (λ (_, val) => val)

  -- Squeeze (line 559)
  def hash_words (c: ValidCircuit P P_Prime) (round: ℕ): (Fin 4) → ZMod P
    | 0 => s c round 0 0
    | 1 => s c round 1 0
    | 2 => s c round 2 0
    | 3 => s c round 3 0

  -- Verify if we converted the correct words to bytes on previous rows
  def squeeze_verify_packed (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 4): Prop :=
    start_new_hash c (get_num_rows_per_round * round) → hash_words c round idx = squeeze_from c (round-1-↑idx)

  def hash_bytes_le (c: ValidCircuit P P_Prime) (round: ℕ) := (hash_bytes c round).reverse

  def squeeze_rlc (c: ValidCircuit P P_Prime) (round: ℕ) := ComposeRlc.expr (hash_bytes_le c round) (c.get_challenge 0 0)

  def hash_rlc_check (c: ValidCircuit P P_Prime) (round: ℕ): Prop :=
    start_new_hash c (get_num_rows_per_round * round) →
      squeeze_rlc c round = hash_rlc c (get_num_rows_per_round * round)

  -- Some general input checks (line 592)
  def boolean_is_final (c: ValidCircuit P P_Prime): Prop :=
    ∀ round ≤ 25, is_final c (12*round) = 0 ∨ is_final c (12*round) = 1

  -- Enforce fixed values on the first row (line 602)
  def is_final_disabled_on_first_row (c: ValidCircuit P P_Prime): Prop :=
    is_final c 0 = 0

  -- Enforce logic for when this block is the last block for a hash (line 612)
  def last_is_padding_in_block (c: ValidCircuit P P_Prime) (round: ℕ): ZMod P :=
    is_paddings c (round - (NUM_ROUNDS + 1 - NUM_WORDS_TO_ABSORB)) (-1)

  def is_final_eq_last_is_padding (c: ValidCircuit P P_Prime): Prop :=
    is_final c (get_num_rows_per_round * 25) = last_is_padding_in_block c 25

  def is_final_only_when_q_enable (c: ValidCircuit P P_Prime) (row: ℕ): Prop :=
    is_final c row = 1 → Selectors.q_enable c row = 1

  -- Padding (line 646)

  def is_padding_boolean (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 8): Prop :=
    is_paddings c round idx = 0 ∨ is_paddings c round idx = 1

  def last_is_padding_zero_on_absorb_rows (c: ValidCircuit P P_Prime) (round: ℕ): Prop :=
    (round = 0 ∨ round = 25) → is_paddings c round (-1) = 0

  def is_padding_prev (c: ValidCircuit P P_Prime) (round: ℕ): (Fin 8) → ZMod P
    | 0 => is_paddings c (round-1) (-1)
    | x => is_paddings c round (x-1)

  def is_first_padding (c: ValidCircuit P P_Prime) (round: ℕ) (idx: Fin 8): ZMod P :=
    is_paddings c round idx - is_padding_prev c round idx

  def padding_step_boolean (c: ValidCircuit P P_Prime) (round: Finset.Icc 1 17): Prop :=
    ∀ idx,
      is_first_padding c round idx = 0 ∨
      is_first_padding c round idx = 1

  def padding_start_intermediate_byte (c: ValidCircuit P P_Prime) (round: Finset.Icc 1 17): Prop :=
    ∀ idx, idx ≠ -1 → is_paddings c round idx = 1 →
      (input_bytes c round).1[idx]? = .some (8, is_first_padding c round idx)

  def padding_start_intermediate_byte_last_byte (c: ValidCircuit P P_Prime) (round: Finset.Icc 1 16): Prop :=
    let idx := -1
    is_paddings c round idx = 1 →
      (input_bytes c round).1[idx]? = .some (8, is_first_padding c round idx)

  def padding_start_end_byte (c: ValidCircuit P P_Prime): Prop :=
    let idx := -1
    is_paddings c 17 idx = 1 →
      (input_bytes c 17).1[idx]? = .some (8, is_first_padding c 17 idx + 128)

  -- Length and data rlc (line 737)
  def update_length (c: ValidCircuit P P_Prime) (round: Finset.Icc 1 17): Prop :=
    (start_new_hash c (get_num_rows_per_round * (round-1)) → (
      length c (get_num_rows_per_round * round) =
        (1 - is_paddings c round 0) +
        (1 - is_paddings c round 1) +
        (1 - is_paddings c round 2) +
        (1 - is_paddings c round 3) +
        (1 - is_paddings c round 4) +
        (1 - is_paddings c round 5) +
        (1 - is_paddings c round 6) +
        (1 - is_paddings c round 7)
    )) ∧
    (¬start_new_hash c (get_num_rows_per_round * (round-1)) → (
      length c (get_num_rows_per_round * round) =
         length c (get_num_rows_per_round*(round-1)) +
            (1 - is_paddings c round 0) +
            (1 - is_paddings c round 1) +
            (1 - is_paddings c round 2) +
            (1 - is_paddings c round 3) +
            (1 - is_paddings c round 4) +
            (1 - is_paddings c round 5) +
            (1 - is_paddings c round 6) +
            (1 - is_paddings c round 7)
    ))

  def initial_data_rlc (c: ValidCircuit P P_Prime) (round: Finset.Icc 1 17): Prop :=
    (start_new_hash c (get_num_rows_per_round * (round-1)) → (
      data_rlc c (get_num_rows_per_round*round + NUM_BYTES_PER_WORD) = 0
    )) ∧
    (¬start_new_hash c (get_num_rows_per_round * (round-1)) → (
      data_rlc c (get_num_rows_per_round*round + NUM_BYTES_PER_WORD) = data_rlc c (get_num_rows_per_round*(round-1))
    ))

  def intermediate_data_rlc (c: ValidCircuit P P_Prime) (round: Finset.Icc 1 17): Prop :=
    ∀ idx,
      (is_paddings c round idx = 0 ∧ data_rlc c (12*↑round + NUM_BYTES_PER_WORD - (↑idx + 1)) = data_rlc c (12*round + 8 - ↑idx) * c.get_challenge 1 0 + (input_bytes c round).1[idx].2) ∨
      (is_paddings c round idx = 1 ∧ data_rlc c (12*↑round + NUM_BYTES_PER_WORD - (↑idx + 1)) = data_rlc c (12*round + 8 - ↑idx))

  def length_equality_check (c: ValidCircuit P P_Prime) (round: Finset.Icc 18 25): Prop :=
    length c (get_num_rows_per_round * round) = length c (get_num_rows_per_round * (round-1))

  def data_rlc_equality_check (c: ValidCircuit P P_Prime) (round: Finset.Icc 18 25): Prop :=
    data_rlc c (get_num_rows_per_round * round) = data_rlc c (get_num_rows_per_round * (round-1))
end Keccak

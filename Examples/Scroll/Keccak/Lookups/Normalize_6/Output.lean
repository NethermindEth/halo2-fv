import Examples.Scroll.Keccak.Constants

namespace Keccak.Lookups.Normalize_6
  -- columns 8 and 9
  -- range = 3
  -- log_height = KECCAK_DEGREE
  -- def part_size := get_num_bits_per_lookup 6

  -- the number of args to input and output
  -- lemma part_size_val: part_size = 3 := by
  --   rewrite [part_size, get_num_bits_per_lookup]
  --   rewrite [Nat.log_eq_iff] <;> decide

  def output (P: ℕ) (x0 x1 x2: ℕ): ZMod P :=
    ↑(([x0, x1, x2].foldl (
      λ (⟨output, factor⟩: ℕ × ℕ) (input_part: ℕ) =>
        (output + (input_part % 2)*factor, factor * BIT_SIZE)
    ) (0, 1): ℕ × ℕ).1)

  def output_by_row (P: ℕ) (row: ℕ) : ZMod P :=
    output P (row / 36) ((row / 6) % 6) (row % 6)

  lemma output_eval: output P x0 x1 x2 =
    ↑(x0 % 2) +
    ↑(x1 % 2) * BIT_SIZE +
    ↑(x2 % 2) * BIT_SIZE ^ 2
    := by
      simp [output, ←pow_two, ←Nat.pow_add_one]

  lemma fixed_func_col_13_0_to_9_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 0 10): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_0_to_9, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_10_to_19_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 10 20): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_10_to_19, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_20_to_29_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 20 30): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_20_to_29, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_30_to_39_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 30 40): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_30_to_39, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_40_to_49_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 40 50): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_40_to_49, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_50_to_59_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 50 60): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_50_to_59, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_60_to_69_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 60 70): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_60_to_69, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_70_to_79_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 70 80): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_70_to_79, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_80_to_89_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 80 90): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_80_to_89, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_90_to_99_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 90 100): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_0_to_99, fixed_func_col_13_90_to_99, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_100_to_109_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 100 110): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_100_to_109, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_110_to_119_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 110 120): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_110_to_119, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_120_to_129_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 120 130): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_120_to_129, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_130_to_139_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 130 140): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_130_to_139, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_140_to_149_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 140 150): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_140_to_149, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_150_to_159_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 150 160): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_150_to_159, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_160_to_169_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 160 170): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_160_to_169, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_170_to_179_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 170 180): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_170_to_179, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_180_to_189_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 180 190): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_180_to_189, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_190_to_199_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 190 200): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_100_to_199, fixed_func_col_13_190_to_199, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_200_to_209_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 200 210): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, fixed_func_col_13_200_to_209, output_by_row, output, keccak_constants]
  lemma fixed_func_col_13_210_to_215_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 210 216): fixed_func_col_13 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_13, output_by_row, output, keccak_constants]

  lemma fixed_func_col_13_0_to_215_output (c : ValidCircuit P P_Prime) (n : Fin 216) :
    fixed_func_col_13 c n = output_by_row P n := by
      rcases n with ⟨n, hn⟩
      by_cases h100: n < 100
      . by_cases h10: n < 10; exact fixed_func_col_13_0_to_9_output c ⟨n, Finset.mem_Ico.mpr ⟨(Nat.zero_le n), h10⟩⟩
        by_cases h20: n < 20; exact fixed_func_col_13_10_to_19_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h10, h20⟩⟩
        by_cases h30: n < 30; exact fixed_func_col_13_20_to_29_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h20, h30⟩⟩
        by_cases h40: n < 40; exact fixed_func_col_13_30_to_39_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h30, h40⟩⟩
        by_cases h50: n < 50; exact fixed_func_col_13_40_to_49_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h40, h50⟩⟩
        by_cases h60: n < 60; exact fixed_func_col_13_50_to_59_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h50, h60⟩⟩
        by_cases h70: n < 70; exact fixed_func_col_13_60_to_69_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h60, h70⟩⟩
        by_cases h80: n < 80; exact fixed_func_col_13_70_to_79_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h70, h80⟩⟩
        by_cases h90: n < 90; exact fixed_func_col_13_80_to_89_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h80, h90⟩⟩
        exact fixed_func_col_13_90_to_99_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h90, h100⟩⟩
      by_cases h200: n < 200
      . by_cases h110: n < 110; exact fixed_func_col_13_100_to_109_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h100, h110⟩⟩
        by_cases h120: n < 120; exact fixed_func_col_13_110_to_119_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h110, h120⟩⟩
        by_cases h130: n < 130; exact fixed_func_col_13_120_to_129_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h120, h130⟩⟩
        by_cases h140: n < 140; exact fixed_func_col_13_130_to_139_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h130, h140⟩⟩
        by_cases h150: n < 150; exact fixed_func_col_13_140_to_149_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h140, h150⟩⟩
        by_cases h160: n < 160; exact fixed_func_col_13_150_to_159_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h150, h160⟩⟩
        by_cases h170: n < 170; exact fixed_func_col_13_160_to_169_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h160, h170⟩⟩
        by_cases h180: n < 180; exact fixed_func_col_13_170_to_179_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h170, h180⟩⟩
        by_cases h190: n < 190; exact fixed_func_col_13_180_to_189_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h180, h190⟩⟩
        exact fixed_func_col_13_190_to_199_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h190, h200⟩⟩
      by_cases h210: n < 210; exact fixed_func_col_13_200_to_209_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h200, h210⟩⟩
      exact fixed_func_col_13_210_to_215_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h210, hn⟩⟩

  lemma fixed_func_col_13_eq_output_of_lt_usable_rows (c: ValidCircuit P P_Prime) (n: ℕ) (hn: n < c.usable_rows):
    fixed_func_col_13 c n = output_by_row P (if n < 216 then n else 0) := by
      split
      case isTrue h => exact fixed_func_col_13_0_to_215_output c ⟨n, h⟩
      case isFalse h =>
        unfold fixed_func_col_13
        rewrite [
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega)
        ]
        simp [output_by_row, output]

end Keccak.Lookups.Normalize_6

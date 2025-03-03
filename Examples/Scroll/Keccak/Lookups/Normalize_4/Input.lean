import Examples.Scroll.Keccak.Constants

namespace Keccak.Lookups.Normalize_4
  -- columns 10 and 11
  -- range = 4
  -- log_height = KECCAK_DEGREE
  -- def part_size := get_num_bits_per_lookup 4

  -- the number of args to input and output
  -- lemma part_size_val: part_size = 4 := by
  --   rewrite [part_size, get_num_bits_per_lookup]
  --   rewrite [Nat.log_eq_iff] <;> decide

  def input (P: ℕ) (x0 x1 x2 x3: ℕ): ZMod P :=
    ↑(([x0, x1, x2, x3].foldl (
      λ (⟨input, factor⟩: ℕ × ℕ) (input_part: ℕ) =>
        (input + input_part*factor, factor * BIT_SIZE)
    ) (0, 1): ℕ × ℕ).1)

  def input_by_row (P: ℕ) (row: ℕ) : ZMod P :=
    input P (row / 64) ((row / 16) % 4) ((row / 4) % 4) (row % 4)

  lemma input_eval: input P x0 x1 x2 x3 =
    x0 +
    x1*BIT_SIZE +
    x2*BIT_SIZE^2 +
    x3*BIT_SIZE^3
    := by
      simp [input, ←pow_two, ←Nat.pow_add_one]

  lemma fixed_func_col_10_0_to_9_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 0 10): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_0_to_9, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_10_to_19_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 10 20): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_10_to_19, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_20_to_29_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 20 30): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_20_to_29, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_30_to_39_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 30 40): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_30_to_39, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_40_to_49_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 40 50): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_40_to_49, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_50_to_59_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 50 60): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_50_to_59, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_60_to_69_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 60 70): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_60_to_69, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_70_to_79_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 70 80): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_70_to_79, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_80_to_89_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 80 90): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_80_to_89, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_90_to_99_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 90 100): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_0_to_99, fixed_func_col_10_90_to_99, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_100_to_109_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 100 110): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_100_to_109, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_110_to_119_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 110 120): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_110_to_119, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_120_to_129_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 120 130): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_120_to_129, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_130_to_139_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 130 140): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_130_to_139, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_140_to_149_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 140 150): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_140_to_149, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_150_to_159_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 150 160): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_150_to_159, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_160_to_169_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 160 170): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_160_to_169, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_170_to_179_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 170 180): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_170_to_179, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_180_to_189_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 180 190): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_180_to_189, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_190_to_199_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 190 200): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_100_to_199, fixed_func_col_10_190_to_199, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_200_to_209_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 200 210): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_200_to_254, fixed_func_col_10_200_to_209, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_210_to_219_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 210 220): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_200_to_254, fixed_func_col_10_210_to_219, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_220_to_229_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 220 230): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_200_to_254, fixed_func_col_10_220_to_229, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_230_to_239_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 230 240): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_200_to_254, fixed_func_col_10_230_to_239, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_240_to_249_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 240 250): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_200_to_254, fixed_func_col_10_240_to_249, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_250_to_255_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 250 256): fixed_func_col_10 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_10, fixed_func_col_10_200_to_254, input_by_row, input, keccak_constants]
  lemma fixed_func_col_10_0_to_255_input (c : ValidCircuit P P_Prime) (n : Fin 256) :
    fixed_func_col_10 c n = input_by_row P n := by
      rcases n with ⟨n, hn⟩
      by_cases h100: n < 100
      . by_cases h10: n < 10; exact fixed_func_col_10_0_to_9_input c ⟨n, Finset.mem_Ico.mpr ⟨(Nat.zero_le n), h10⟩⟩
        by_cases h20: n < 20; exact fixed_func_col_10_10_to_19_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h10, h20⟩⟩
        by_cases h30: n < 30; exact fixed_func_col_10_20_to_29_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h20, h30⟩⟩
        by_cases h40: n < 40; exact fixed_func_col_10_30_to_39_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h30, h40⟩⟩
        by_cases h50: n < 50; exact fixed_func_col_10_40_to_49_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h40, h50⟩⟩
        by_cases h60: n < 60; exact fixed_func_col_10_50_to_59_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h50, h60⟩⟩
        by_cases h70: n < 70; exact fixed_func_col_10_60_to_69_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h60, h70⟩⟩
        by_cases h80: n < 80; exact fixed_func_col_10_70_to_79_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h70, h80⟩⟩
        by_cases h90: n < 90; exact fixed_func_col_10_80_to_89_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h80, h90⟩⟩
        exact fixed_func_col_10_90_to_99_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h90, h100⟩⟩
      by_cases h200: n < 200
      . by_cases h110: n < 110; exact fixed_func_col_10_100_to_109_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h100, h110⟩⟩
        by_cases h120: n < 120; exact fixed_func_col_10_110_to_119_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h110, h120⟩⟩
        by_cases h130: n < 130; exact fixed_func_col_10_120_to_129_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h120, h130⟩⟩
        by_cases h140: n < 140; exact fixed_func_col_10_130_to_139_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h130, h140⟩⟩
        by_cases h150: n < 150; exact fixed_func_col_10_140_to_149_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h140, h150⟩⟩
        by_cases h160: n < 160; exact fixed_func_col_10_150_to_159_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h150, h160⟩⟩
        by_cases h170: n < 170; exact fixed_func_col_10_160_to_169_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h160, h170⟩⟩
        by_cases h180: n < 180; exact fixed_func_col_10_170_to_179_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h170, h180⟩⟩
        by_cases h190: n < 190; exact fixed_func_col_10_180_to_189_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h180, h190⟩⟩
        exact fixed_func_col_10_190_to_199_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h190, h200⟩⟩
      by_cases h210: n < 210; exact fixed_func_col_10_200_to_209_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h200, h210⟩⟩
      by_cases h220: n < 220; exact fixed_func_col_10_210_to_219_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h210, h220⟩⟩
      by_cases h230: n < 230; exact fixed_func_col_10_220_to_229_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h220, h230⟩⟩
      by_cases h240: n < 240; exact fixed_func_col_10_230_to_239_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h230, h240⟩⟩
      by_cases h250: n < 250; exact fixed_func_col_10_240_to_249_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h240, h250⟩⟩
      exact fixed_func_col_10_250_to_255_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h250, hn⟩⟩

  lemma fixed_func_col_10_eq_input_of_lt_usable_rows (c: ValidCircuit P P_Prime) (n: ℕ) (hn: n < c.usable_rows):
    fixed_func_col_10 c n = input_by_row P (if n < 256 then n else 0) := by
      split
      case isTrue h => exact fixed_func_col_10_0_to_255_input c ⟨n, h⟩
      case isFalse h =>
        unfold fixed_func_col_10
        rewrite [
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega)
        ]
        simp [input_by_row, input]

end Keccak.Lookups.Normalize_4

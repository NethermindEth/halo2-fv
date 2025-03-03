import Examples.Scroll.Keccak.Constants

namespace Keccak.Lookups.Normalize_3
  -- columns 8 and 9
  -- range = 3
  -- log_height = KECCAK_DEGREE
  -- def part_size := get_num_bits_per_lookup 3

  -- the number of args to input and output
  -- lemma part_size_val: part_size = 6 := by
  --   rewrite [part_size, get_num_bits_per_lookup]
  --   rewrite [Nat.log_eq_iff] <;> decide

  def input (P: ℕ) (x0 x1 x2 x3 x4 x5: ℕ): ZMod P :=
    ↑(([x0, x1, x2, x3, x4, x5].foldl (
      λ (⟨input, factor⟩: ℕ × ℕ) (input_part: ℕ) =>
        (input + input_part*factor, factor * BIT_SIZE)
    ) (0, 1): ℕ × ℕ).1)

  def input_by_row (P: ℕ) (row: ℕ) : ZMod P :=
    input P (row / 243) ((row / 81) % 3) ((row / 27) % 3) ((row / 9) % 3) ((row / 3) % 3) (row % 3)

  lemma input_eval: input P x0 x1 x2 x3 x4 x5 =
    x0 +
    x1*BIT_SIZE +
    x2*BIT_SIZE^2 +
    x3*BIT_SIZE^3 +
    x4*BIT_SIZE^4 +
    x5*BIT_SIZE^5
    := by
      simp [input, ←pow_two, ←Nat.pow_add_one]

  lemma fixed_func_col_8_0_to_9_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 0 10): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_0_to_9, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_10_to_19_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 10 20): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_10_to_19, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_20_to_29_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 20 30): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_20_to_29, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_30_to_39_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 30 40): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_30_to_39, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_40_to_49_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 40 50): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_40_to_49, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_50_to_59_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 50 60): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_50_to_59, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_60_to_69_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 60 70): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_60_to_69, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_70_to_79_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 70 80): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_70_to_79, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_80_to_89_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 80 90): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_80_to_89, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_90_to_99_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 90 100): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_0_to_99, fixed_func_col_8_90_to_99, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_100_to_109_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 100 110): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_100_to_109, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_110_to_119_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 110 120): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_110_to_119, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_120_to_129_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 120 130): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_120_to_129, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_130_to_139_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 130 140): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_130_to_139, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_140_to_149_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 140 150): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_140_to_149, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_150_to_159_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 150 160): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_150_to_159, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_160_to_169_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 160 170): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_160_to_169, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_170_to_179_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 170 180): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_170_to_179, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_180_to_189_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 180 190): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_180_to_189, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_190_to_199_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 190 200): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_100_to_199, fixed_func_col_8_190_to_199, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_200_to_209_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 200 210): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_200_to_209, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_210_to_219_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 210 220): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_210_to_219, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_220_to_229_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 220 230): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_220_to_229, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_230_to_239_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 230 240): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_230_to_239, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_240_to_249_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 240 250): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_240_to_249, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_250_to_259_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 250 260): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_250_to_259, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_260_to_269_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 260 270): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_260_to_269, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_270_to_279_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 270 280): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_270_to_279, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_280_to_289_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 280 290): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_280_to_289, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_290_to_299_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 290 300): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_200_to_299, fixed_func_col_8_290_to_299, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_300_to_309_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 300 310): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_300_to_309, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_310_to_319_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 310 320): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_310_to_319, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_320_to_329_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 320 330): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_320_to_329, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_330_to_339_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 330 340): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_330_to_339, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_340_to_349_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 340 350): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_340_to_349, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_350_to_359_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 350 360): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_350_to_359, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_360_to_369_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 360 370): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_360_to_369, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_370_to_379_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 370 380): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_370_to_379, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_380_to_389_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 380 390): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_380_to_389, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_390_to_399_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 390 400): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_300_to_399, fixed_func_col_8_390_to_399, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_400_to_409_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 400 410): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_400_to_409, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_410_to_419_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 410 420): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_410_to_419, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_420_to_429_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 420 430): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_420_to_429, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_430_to_439_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 430 440): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_430_to_439, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_440_to_449_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 440 450): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_440_to_449, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_450_to_459_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 450 460): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_450_to_459, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_460_to_469_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 460 470): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_460_to_469, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_470_to_479_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 470 480): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_470_to_479, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_480_to_489_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 480 490): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_480_to_489, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_490_to_499_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 490 500): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_400_to_499, fixed_func_col_8_490_to_499, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_500_to_509_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 500 510): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_500_to_509, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_510_to_519_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 510 520): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_510_to_519, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_520_to_529_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 520 530): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_520_to_529, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_530_to_539_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 530 540): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_530_to_539, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_540_to_549_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 540 550): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_540_to_549, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_550_to_559_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 550 560): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_550_to_559, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_560_to_569_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 560 570): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_560_to_569, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_570_to_579_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 570 580): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_570_to_579, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_580_to_589_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 580 590): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_580_to_589, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_590_to_599_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 590 600): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_500_to_599, fixed_func_col_8_590_to_599, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_600_to_609_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 600 610): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_600_to_609, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_610_to_619_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 610 620): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_610_to_619, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_620_to_629_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 620 630): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_620_to_629, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_630_to_639_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 630 640): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_630_to_639, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_640_to_649_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 640 650): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_640_to_649, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_650_to_659_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 650 660): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_650_to_659, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_660_to_669_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 660 670): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_660_to_669, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_670_to_679_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 670 680): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_670_to_679, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_680_to_689_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 680 690): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_680_to_689, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_690_to_699_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 690 700): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_600_to_699, fixed_func_col_8_690_to_699, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_700_to_709_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 700 710): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_700_to_727, fixed_func_col_8_700_to_709, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_710_to_719_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 710 720): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_700_to_727, fixed_func_col_8_710_to_719, input_by_row, input, keccak_constants]
  lemma fixed_func_col_8_720_to_728_input (c: ValidCircuit P P_Prime) (n: Finset.Ico 720 729): fixed_func_col_8 c n = input_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_8, fixed_func_col_8_700_to_727, input_by_row, input, keccak_constants]

  lemma fixed_func_col_8_0_to_728_input (c : ValidCircuit P P_Prime) (n : Fin 729) :
    fixed_func_col_8 c n = input_by_row P n := by
      rcases n with ⟨n, hn⟩
      by_cases h100: n < 100
      . by_cases h10: n < 10; exact fixed_func_col_8_0_to_9_input c ⟨n, Finset.mem_Ico.mpr ⟨(Nat.zero_le n), h10⟩⟩
        by_cases h20: n < 20; exact fixed_func_col_8_10_to_19_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h10, h20⟩⟩
        by_cases h30: n < 30; exact fixed_func_col_8_20_to_29_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h20, h30⟩⟩
        by_cases h40: n < 40; exact fixed_func_col_8_30_to_39_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h30, h40⟩⟩
        by_cases h50: n < 50; exact fixed_func_col_8_40_to_49_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h40, h50⟩⟩
        by_cases h60: n < 60; exact fixed_func_col_8_50_to_59_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h50, h60⟩⟩
        by_cases h70: n < 70; exact fixed_func_col_8_60_to_69_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h60, h70⟩⟩
        by_cases h80: n < 80; exact fixed_func_col_8_70_to_79_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h70, h80⟩⟩
        by_cases h90: n < 90; exact fixed_func_col_8_80_to_89_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h80, h90⟩⟩
        exact fixed_func_col_8_90_to_99_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h90, h100⟩⟩
      by_cases h200: n < 200
      . by_cases h110: n < 110; exact fixed_func_col_8_100_to_109_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h100, h110⟩⟩
        by_cases h120: n < 120; exact fixed_func_col_8_110_to_119_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h110, h120⟩⟩
        by_cases h130: n < 130; exact fixed_func_col_8_120_to_129_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h120, h130⟩⟩
        by_cases h140: n < 140; exact fixed_func_col_8_130_to_139_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h130, h140⟩⟩
        by_cases h150: n < 150; exact fixed_func_col_8_140_to_149_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h140, h150⟩⟩
        by_cases h160: n < 160; exact fixed_func_col_8_150_to_159_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h150, h160⟩⟩
        by_cases h170: n < 170; exact fixed_func_col_8_160_to_169_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h160, h170⟩⟩
        by_cases h180: n < 180; exact fixed_func_col_8_170_to_179_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h170, h180⟩⟩
        by_cases h190: n < 190; exact fixed_func_col_8_180_to_189_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h180, h190⟩⟩
        exact fixed_func_col_8_190_to_199_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h190, h200⟩⟩
      by_cases h300: n < 300
      . by_cases h210: n < 210; exact fixed_func_col_8_200_to_209_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h200, h210⟩⟩
        by_cases h220: n < 220; exact fixed_func_col_8_210_to_219_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h210, h220⟩⟩
        by_cases h230: n < 230; exact fixed_func_col_8_220_to_229_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h220, h230⟩⟩
        by_cases h240: n < 240; exact fixed_func_col_8_230_to_239_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h230, h240⟩⟩
        by_cases h250: n < 250; exact fixed_func_col_8_240_to_249_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h240, h250⟩⟩
        by_cases h260: n < 260; exact fixed_func_col_8_250_to_259_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h250, h260⟩⟩
        by_cases h270: n < 270; exact fixed_func_col_8_260_to_269_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h260, h270⟩⟩
        by_cases h280: n < 280; exact fixed_func_col_8_270_to_279_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h270, h280⟩⟩
        by_cases h290: n < 290; exact fixed_func_col_8_280_to_289_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h280, h290⟩⟩
        exact fixed_func_col_8_290_to_299_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h290, h300⟩⟩
      by_cases h400: n < 400
      . by_cases h310: n < 310; exact fixed_func_col_8_300_to_309_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h300, h310⟩⟩
        by_cases h320: n < 320; exact fixed_func_col_8_310_to_319_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h310, h320⟩⟩
        by_cases h330: n < 330; exact fixed_func_col_8_320_to_329_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h320, h330⟩⟩
        by_cases h340: n < 340; exact fixed_func_col_8_330_to_339_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h330, h340⟩⟩
        by_cases h350: n < 350; exact fixed_func_col_8_340_to_349_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h340, h350⟩⟩
        by_cases h360: n < 360; exact fixed_func_col_8_350_to_359_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h350, h360⟩⟩
        by_cases h370: n < 370; exact fixed_func_col_8_360_to_369_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h360, h370⟩⟩
        by_cases h380: n < 380; exact fixed_func_col_8_370_to_379_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h370, h380⟩⟩
        by_cases h390: n < 390; exact fixed_func_col_8_380_to_389_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h380, h390⟩⟩
        exact fixed_func_col_8_390_to_399_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h390, h400⟩⟩
      by_cases h500: n < 500
      . by_cases h410: n < 410; exact fixed_func_col_8_400_to_409_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h400, h410⟩⟩
        by_cases h420: n < 420; exact fixed_func_col_8_410_to_419_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h410, h420⟩⟩
        by_cases h430: n < 430; exact fixed_func_col_8_420_to_429_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h420, h430⟩⟩
        by_cases h440: n < 440; exact fixed_func_col_8_430_to_439_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h430, h440⟩⟩
        by_cases h450: n < 450; exact fixed_func_col_8_440_to_449_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h440, h450⟩⟩
        by_cases h460: n < 460; exact fixed_func_col_8_450_to_459_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h450, h460⟩⟩
        by_cases h470: n < 470; exact fixed_func_col_8_460_to_469_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h460, h470⟩⟩
        by_cases h480: n < 480; exact fixed_func_col_8_470_to_479_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h470, h480⟩⟩
        by_cases h490: n < 490; exact fixed_func_col_8_480_to_489_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h480, h490⟩⟩
        exact fixed_func_col_8_490_to_499_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h490, h500⟩⟩
      by_cases h600: n < 600
      . by_cases h510: n < 510; exact fixed_func_col_8_500_to_509_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h500, h510⟩⟩
        by_cases h520: n < 520; exact fixed_func_col_8_510_to_519_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h510, h520⟩⟩
        by_cases h530: n < 530; exact fixed_func_col_8_520_to_529_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h520, h530⟩⟩
        by_cases h540: n < 540; exact fixed_func_col_8_530_to_539_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h530, h540⟩⟩
        by_cases h550: n < 550; exact fixed_func_col_8_540_to_549_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h540, h550⟩⟩
        by_cases h560: n < 560; exact fixed_func_col_8_550_to_559_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h550, h560⟩⟩
        by_cases h570: n < 570; exact fixed_func_col_8_560_to_569_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h560, h570⟩⟩
        by_cases h580: n < 580; exact fixed_func_col_8_570_to_579_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h570, h580⟩⟩
        by_cases h590: n < 590; exact fixed_func_col_8_580_to_589_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h580, h590⟩⟩
        exact fixed_func_col_8_590_to_599_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h590, h600⟩⟩
      by_cases h700: n < 700
      . by_cases h610: n < 610; exact fixed_func_col_8_600_to_609_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h600, h610⟩⟩
        by_cases h620: n < 620; exact fixed_func_col_8_610_to_619_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h610, h620⟩⟩
        by_cases h630: n < 630; exact fixed_func_col_8_620_to_629_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h620, h630⟩⟩
        by_cases h640: n < 640; exact fixed_func_col_8_630_to_639_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h630, h640⟩⟩
        by_cases h650: n < 650; exact fixed_func_col_8_640_to_649_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h640, h650⟩⟩
        by_cases h660: n < 660; exact fixed_func_col_8_650_to_659_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h650, h660⟩⟩
        by_cases h670: n < 670; exact fixed_func_col_8_660_to_669_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h660, h670⟩⟩
        by_cases h680: n < 680; exact fixed_func_col_8_670_to_679_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h670, h680⟩⟩
        by_cases h690: n < 690; exact fixed_func_col_8_680_to_689_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h680, h690⟩⟩
        exact fixed_func_col_8_690_to_699_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h690, h700⟩⟩
      by_cases h710: n < 710; exact fixed_func_col_8_700_to_709_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h700, h710⟩⟩
      by_cases h720: n < 720; exact fixed_func_col_8_710_to_719_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h710, h720⟩⟩
      exact fixed_func_col_8_720_to_728_input c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h720, hn⟩⟩

  lemma fixed_func_col_8_eq_input_of_lt_usable_rows (c: ValidCircuit P P_Prime) (n: ℕ) (hn: n < c.usable_rows):
    fixed_func_col_8 c n = input_by_row P (if n < 729 then n else 0) := by
      split
      case isTrue h => exact fixed_func_col_8_0_to_728_input c ⟨n, h⟩
      case isFalse h =>
        unfold fixed_func_col_8
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
        simp [input_by_row, input]

end Keccak.Lookups.Normalize_3

import Examples.Scroll.Keccak.Constants

namespace Keccak.Lookups.ChiBase
  -- columns 14 and 15
  -- def part_size := get_num_bits_per_base_chi_lookup

  -- the number of args to input and output
  -- lemma part_size_val: part_size = 4 := by simp [part_size, keccak_constants]

  def output (P: ℕ) (x0 x1 x2 x3: Fin 5): ZMod P :=
    ↑(([x0, x1, x2, x3].foldl (
      λ (⟨output, factor⟩: ℕ × ℕ) (input_part: ℕ) =>
        (output + (CHI_BASE_LOOKUP_TABLE input_part)*factor, factor * BIT_SIZE)
    ) (0, 1): ℕ × ℕ).1)

  def output_by_row (P: ℕ) (row: ℕ) : ZMod P :=
    output P ↑((row / 125) % 5) ↑((row / 25) % 5) ↑((row / 5) % 5) ↑(row % 5)

  lemma output_eval: output P x0 x1 x2 x3 =
    ↑(CHI_BASE_LOOKUP_TABLE x0) +
    ↑(CHI_BASE_LOOKUP_TABLE x1) * BIT_SIZE +
    ↑(CHI_BASE_LOOKUP_TABLE x2) * BIT_SIZE ^ 2 +
    ↑(CHI_BASE_LOOKUP_TABLE x3) * BIT_SIZE ^ 3
    := by
      simp [output, ←pow_two, ←Nat.pow_add_one]

  lemma fin_last_4: Fin.last (@Fin.val 5 4) = 4 := by rfl

  lemma fixed_func_col_15_0_to_9_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 0 10): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_0_to_17, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_10_to_19_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 10 20): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_0_to_17, fixed_func_col_15_18_to_37, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_20_to_29_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 20 30): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_0_to_17, fixed_func_col_15_18_to_37, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_30_to_39_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 30 40): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_18_to_37, fixed_func_col_15_38_to_57, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_40_to_49_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 40 50): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_38_to_57, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_50_to_59_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 50 60): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_38_to_57, fixed_func_col_15_58_to_77, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_60_to_69_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 60 70): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_58_to_77, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_70_to_79_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 70 80): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_58_to_77, fixed_func_col_15_78_to_97, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_80_to_89_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 80 90): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_78_to_97, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_90_to_99_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 90 100): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_78_to_97, fixed_func_col_15_98_to_117, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_100_to_109_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 100 110): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_98_to_117, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_110_to_119_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 110 120): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_98_to_117, fixed_func_col_15_118_to_137, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_120_to_129_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 120 130): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_118_to_137, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_130_to_139_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 130 140): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_118_to_137, fixed_func_col_15_138_to_155, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_140_to_149_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 140 150): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_138_to_155, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_150_to_159_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 150 160): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_138_to_155, fixed_func_col_15_156_to_177, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_160_to_169_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 160 170): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_156_to_177, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_170_to_179_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 170 180): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_156_to_177, fixed_func_col_15_178_to_197, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_180_to_189_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 180 190): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_178_to_197, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_190_to_199_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 190 200): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_0_to_197, fixed_func_col_15_178_to_197, fixed_func_col_15_198_to_397, fixed_func_col_15_198_to_215, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_200_to_209_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 200 210): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_198_to_215, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_210_to_219_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 210 220): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_198_to_215, fixed_func_col_15_216_to_237, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_220_to_229_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 220 230): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_216_to_237, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_230_to_239_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 230 240): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_216_to_237, fixed_func_col_15_238_to_257, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_240_to_249_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 240 250): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_238_to_257, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_250_to_259_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 250 260): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_238_to_257, fixed_func_col_15_258_to_277, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_260_to_269_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 260 270): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_258_to_277, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_270_to_279_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 270 280): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_258_to_277, fixed_func_col_15_278_to_297, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_280_to_289_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 280 290): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_278_to_297, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_290_to_299_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 290 300): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_278_to_297, fixed_func_col_15_298_to_317, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_300_to_309_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 300 310): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_298_to_317, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_310_to_319_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 310 320): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_298_to_317, fixed_func_col_15_318_to_337, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_320_to_329_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 320 330): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_318_to_337, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_330_to_339_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 330 340): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_318_to_337, fixed_func_col_15_338_to_357, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_340_to_349_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 340 350): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_338_to_357, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_350_to_359_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 350 360): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_338_to_357, fixed_func_col_15_358_to_377, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_360_to_369_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 360 370): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_358_to_377, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_370_to_379_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 370 380): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_358_to_377, fixed_func_col_15_378_to_397, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_380_to_389_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 380 390): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_378_to_397, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_390_to_399_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 390 400): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_198_to_397, fixed_func_col_15_378_to_397, fixed_func_col_15_398_to_597, fixed_func_col_15_398_to_415, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_400_to_409_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 400 410): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_398_to_415, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_410_to_419_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 410 420): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_398_to_415, fixed_func_col_15_416_to_437, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_420_to_429_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 420 430): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_416_to_437, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_430_to_439_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 430 440): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_416_to_437, fixed_func_col_15_438_to_455, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_440_to_449_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 440 450): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_438_to_455, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_450_to_459_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 450 460): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_438_to_455, fixed_func_col_15_456_to_477, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_460_to_469_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 460 470): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_456_to_477, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_470_to_479_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 470 480): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_456_to_477, fixed_func_col_15_478_to_497, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_480_to_489_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 480 490): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_478_to_497, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_490_to_499_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 490 500): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_478_to_497, fixed_func_col_15_498_to_517, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_500_to_509_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 500 510): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_498_to_517, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_510_to_519_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 510 520): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_498_to_517, fixed_func_col_15_518_to_537, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_520_to_529_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 520 530): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_518_to_537, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_530_to_539_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 530 540): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_518_to_537, fixed_func_col_15_538_to_557, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_540_to_549_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 540 550): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_538_to_557, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_550_to_559_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 550 560): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_538_to_557, fixed_func_col_15_558_to_577, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_560_to_569_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 560 570): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_558_to_577, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_570_to_579_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 570 580): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_558_to_577, fixed_func_col_15_578_to_597, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_580_to_589_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 580 590): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_578_to_597, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_590_to_599_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 590 600): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_398_to_597, fixed_func_col_15_578_to_597, fixed_func_col_15_598_to_617, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_600_to_609_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 600 610): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_598_to_617, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_610_to_619_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 610 620): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, fixed_func_col_15_598_to_617, output_by_row, output, keccak_constants, fin_last_4]
  lemma fixed_func_col_15_620_to_624_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 620 625): fixed_func_col_15 c n = output_by_row P n := by
    fin_cases n <;> simp [fixed_func_col_15, output_by_row, output, keccak_constants, fin_last_4]

  lemma fixed_func_col_15_0_to_624_output (c : ValidCircuit P P_Prime) (n : Fin 625) :
    fixed_func_col_15 c n = output_by_row P n := by
      rcases n with ⟨n, hn⟩
      by_cases h100: n < 100
      . by_cases h10: n < 10; exact fixed_func_col_15_0_to_9_output c ⟨n, Finset.mem_Ico.mpr ⟨(Nat.zero_le n), h10⟩⟩
        by_cases h20: n < 20; exact fixed_func_col_15_10_to_19_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h10, h20⟩⟩
        by_cases h30: n < 30; exact fixed_func_col_15_20_to_29_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h20, h30⟩⟩
        by_cases h40: n < 40; exact fixed_func_col_15_30_to_39_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h30, h40⟩⟩
        by_cases h50: n < 50; exact fixed_func_col_15_40_to_49_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h40, h50⟩⟩
        by_cases h60: n < 60; exact fixed_func_col_15_50_to_59_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h50, h60⟩⟩
        by_cases h70: n < 70; exact fixed_func_col_15_60_to_69_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h60, h70⟩⟩
        by_cases h80: n < 80; exact fixed_func_col_15_70_to_79_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h70, h80⟩⟩
        by_cases h90: n < 90; exact fixed_func_col_15_80_to_89_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h80, h90⟩⟩
        exact fixed_func_col_15_90_to_99_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h90, h100⟩⟩
      by_cases h200: n < 200
      . by_cases h110: n < 110; exact fixed_func_col_15_100_to_109_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h100, h110⟩⟩
        by_cases h120: n < 120; exact fixed_func_col_15_110_to_119_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h110, h120⟩⟩
        by_cases h130: n < 130; exact fixed_func_col_15_120_to_129_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h120, h130⟩⟩
        by_cases h140: n < 140; exact fixed_func_col_15_130_to_139_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h130, h140⟩⟩
        by_cases h150: n < 150; exact fixed_func_col_15_140_to_149_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h140, h150⟩⟩
        by_cases h160: n < 160; exact fixed_func_col_15_150_to_159_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h150, h160⟩⟩
        by_cases h170: n < 170; exact fixed_func_col_15_160_to_169_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h160, h170⟩⟩
        by_cases h180: n < 180; exact fixed_func_col_15_170_to_179_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h170, h180⟩⟩
        by_cases h190: n < 190; exact fixed_func_col_15_180_to_189_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h180, h190⟩⟩
        exact fixed_func_col_15_190_to_199_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h190, h200⟩⟩
      by_cases h300: n < 300
      . by_cases h210: n < 210; exact fixed_func_col_15_200_to_209_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h200, h210⟩⟩
        by_cases h220: n < 220; exact fixed_func_col_15_210_to_219_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h210, h220⟩⟩
        by_cases h230: n < 230; exact fixed_func_col_15_220_to_229_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h220, h230⟩⟩
        by_cases h240: n < 240; exact fixed_func_col_15_230_to_239_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h230, h240⟩⟩
        by_cases h250: n < 250; exact fixed_func_col_15_240_to_249_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h240, h250⟩⟩
        by_cases h260: n < 260; exact fixed_func_col_15_250_to_259_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h250, h260⟩⟩
        by_cases h270: n < 270; exact fixed_func_col_15_260_to_269_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h260, h270⟩⟩
        by_cases h280: n < 280; exact fixed_func_col_15_270_to_279_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h270, h280⟩⟩
        by_cases h290: n < 290; exact fixed_func_col_15_280_to_289_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h280, h290⟩⟩
        exact fixed_func_col_15_290_to_299_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h290, h300⟩⟩
      by_cases h400: n < 400
      . by_cases h310: n < 310; exact fixed_func_col_15_300_to_309_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h300, h310⟩⟩
        by_cases h320: n < 320; exact fixed_func_col_15_310_to_319_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h310, h320⟩⟩
        by_cases h330: n < 330; exact fixed_func_col_15_320_to_329_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h320, h330⟩⟩
        by_cases h340: n < 340; exact fixed_func_col_15_330_to_339_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h330, h340⟩⟩
        by_cases h350: n < 350; exact fixed_func_col_15_340_to_349_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h340, h350⟩⟩
        by_cases h360: n < 360; exact fixed_func_col_15_350_to_359_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h350, h360⟩⟩
        by_cases h370: n < 370; exact fixed_func_col_15_360_to_369_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h360, h370⟩⟩
        by_cases h380: n < 380; exact fixed_func_col_15_370_to_379_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h370, h380⟩⟩
        by_cases h390: n < 390; exact fixed_func_col_15_380_to_389_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h380, h390⟩⟩
        exact fixed_func_col_15_390_to_399_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h390, h400⟩⟩
      by_cases h500: n < 500
      . by_cases h410: n < 410; exact fixed_func_col_15_400_to_409_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h400, h410⟩⟩
        by_cases h420: n < 420; exact fixed_func_col_15_410_to_419_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h410, h420⟩⟩
        by_cases h430: n < 430; exact fixed_func_col_15_420_to_429_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h420, h430⟩⟩
        by_cases h440: n < 440; exact fixed_func_col_15_430_to_439_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h430, h440⟩⟩
        by_cases h450: n < 450; exact fixed_func_col_15_440_to_449_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h440, h450⟩⟩
        by_cases h460: n < 460; exact fixed_func_col_15_450_to_459_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h450, h460⟩⟩
        by_cases h470: n < 470; exact fixed_func_col_15_460_to_469_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h460, h470⟩⟩
        by_cases h480: n < 480; exact fixed_func_col_15_470_to_479_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h470, h480⟩⟩
        by_cases h490: n < 490; exact fixed_func_col_15_480_to_489_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h480, h490⟩⟩
        exact fixed_func_col_15_490_to_499_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h490, h500⟩⟩
      by_cases h600: n < 600
      . by_cases h510: n < 510; exact fixed_func_col_15_500_to_509_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h500, h510⟩⟩
        by_cases h520: n < 520; exact fixed_func_col_15_510_to_519_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h510, h520⟩⟩
        by_cases h530: n < 530; exact fixed_func_col_15_520_to_529_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h520, h530⟩⟩
        by_cases h540: n < 540; exact fixed_func_col_15_530_to_539_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h530, h540⟩⟩
        by_cases h550: n < 550; exact fixed_func_col_15_540_to_549_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h540, h550⟩⟩
        by_cases h560: n < 560; exact fixed_func_col_15_550_to_559_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h550, h560⟩⟩
        by_cases h570: n < 570; exact fixed_func_col_15_560_to_569_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h560, h570⟩⟩
        by_cases h580: n < 580; exact fixed_func_col_15_570_to_579_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h570, h580⟩⟩
        by_cases h590: n < 590; exact fixed_func_col_15_580_to_589_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h580, h590⟩⟩
        exact fixed_func_col_15_590_to_599_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h590, h600⟩⟩
      by_cases h610: n < 610; exact fixed_func_col_15_600_to_609_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h600, h610⟩⟩
      by_cases h620: n < 620; exact fixed_func_col_15_610_to_619_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h610, h620⟩⟩
      exact fixed_func_col_15_620_to_624_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h620, hn⟩⟩

  lemma fixed_func_col_15_eq_output_of_lt_usable_rows (c: ValidCircuit P P_Prime) (n: ℕ) (hn: n < c.usable_rows):
    fixed_func_col_15 c n = output_by_row P (if n < 625 then n else 0) := by
      split
      case isTrue h => exact fixed_func_col_15_0_to_624_output c ⟨n, h⟩
      case isFalse h =>
        unfold fixed_func_col_15
        rewrite [
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega)
        ]
        simp [output_by_row, output, keccak_constants]

end Keccak.Lookups.ChiBase

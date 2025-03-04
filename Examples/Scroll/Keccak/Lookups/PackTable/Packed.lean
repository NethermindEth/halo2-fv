import Examples.Scroll.Keccak.Constants

namespace Keccak.Lookups.PackTable
  -- columns 16 and 17

  def into_bits (bytes: List ℕ): List ℕ :=
    (bytes.map (λ byte => (
      (List.range 8).map (λ idx => (
        (byte / (2^idx)) % 2
      ))
    ))).join

  def pack_with_base (P: ℕ) (bits: List ℕ) (base: ℕ): ZMod P :=
    bits.foldr (λ bit acc => acc * base + bit) 0

  def pack (P: ℕ) (bits: List ℕ): ZMod P :=
    pack_with_base P bits BIT_SIZE

  def loop_8: List.range 8 = [0,1,2,3,4,5,6,7] := rfl

  lemma fixed_func_col_17_0_to_9_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 0 10): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_0_to_9, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_10_to_19_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 10 20): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_10_to_19, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_20_to_29_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 20 30): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_20_to_29, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_30_to_39_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 30 40): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_30_to_39, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_40_to_49_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 40 50): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_40_to_49, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_50_to_59_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 50 60): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_50_to_59, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_60_to_69_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 60 70): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_60_to_69, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_70_to_79_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 70 80): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_70_to_79, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_80_to_89_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 80 90): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_80_to_89, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_90_to_99_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 90 100): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_0_to_99, fixed_func_col_17_90_to_99, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_100_to_109_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 100 110): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_100_to_109, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_110_to_119_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 110 120): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_110_to_119, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_120_to_129_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 120 130): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_120_to_129, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_130_to_139_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 130 140): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_130_to_139, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_140_to_149_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 140 150): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_140_to_149, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_150_to_159_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 150 160): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_150_to_159, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_160_to_169_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 160 170): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_160_to_169, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_170_to_179_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 170 180): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_170_to_179, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_180_to_189_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 180 190): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_180_to_189, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_190_to_199_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 190 200): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_100_to_199, fixed_func_col_17_190_to_199, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_200_to_209_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 200 210): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_200_to_254, fixed_func_col_17_200_to_209, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_210_to_219_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 210 220): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_200_to_254, fixed_func_col_17_210_to_219, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_220_to_229_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 220 230): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_200_to_254, fixed_func_col_17_220_to_229, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_230_to_239_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 230 240): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_200_to_254, fixed_func_col_17_230_to_239, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_240_to_249_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 240 250): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_200_to_254, fixed_func_col_17_240_to_249, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num
  lemma fixed_func_col_17_250_to_255_output (c: ValidCircuit P P_Prime) (n: Finset.Ico 250 256): fixed_func_col_17 c n = pack P (into_bits [n]) := by
    fin_cases n <;> simp [fixed_func_col_17, fixed_func_col_17_200_to_254, pack, keccak_constants, pack_with_base, into_bits, loop_8] <;> norm_num

  lemma fixed_func_col_17_0_to_256_output (c : ValidCircuit P P_Prime) (n : Fin 256) :
    fixed_func_col_17 c n = pack P (into_bits [n]) := by
      rcases n with ⟨n, hn⟩
      by_cases h100: n < 100
      . by_cases h10: n < 10; exact fixed_func_col_17_0_to_9_output c ⟨n, Finset.mem_Ico.mpr ⟨(Nat.zero_le n), h10⟩⟩
        by_cases h20: n < 20; exact fixed_func_col_17_10_to_19_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h10, h20⟩⟩
        by_cases h30: n < 30; exact fixed_func_col_17_20_to_29_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h20, h30⟩⟩
        by_cases h40: n < 40; exact fixed_func_col_17_30_to_39_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h30, h40⟩⟩
        by_cases h50: n < 50; exact fixed_func_col_17_40_to_49_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h40, h50⟩⟩
        by_cases h60: n < 60; exact fixed_func_col_17_50_to_59_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h50, h60⟩⟩
        by_cases h70: n < 70; exact fixed_func_col_17_60_to_69_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h60, h70⟩⟩
        by_cases h80: n < 80; exact fixed_func_col_17_70_to_79_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h70, h80⟩⟩
        by_cases h90: n < 90; exact fixed_func_col_17_80_to_89_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h80, h90⟩⟩
        exact fixed_func_col_17_90_to_99_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h90, h100⟩⟩
      by_cases h200: n < 200
      . by_cases h110: n < 110; exact fixed_func_col_17_100_to_109_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h100, h110⟩⟩
        by_cases h120: n < 120; exact fixed_func_col_17_110_to_119_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h110, h120⟩⟩
        by_cases h130: n < 130; exact fixed_func_col_17_120_to_129_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h120, h130⟩⟩
        by_cases h140: n < 140; exact fixed_func_col_17_130_to_139_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h130, h140⟩⟩
        by_cases h150: n < 150; exact fixed_func_col_17_140_to_149_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h140, h150⟩⟩
        by_cases h160: n < 160; exact fixed_func_col_17_150_to_159_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h150, h160⟩⟩
        by_cases h170: n < 170; exact fixed_func_col_17_160_to_169_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h160, h170⟩⟩
        by_cases h180: n < 180; exact fixed_func_col_17_170_to_179_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h170, h180⟩⟩
        by_cases h190: n < 190; exact fixed_func_col_17_180_to_189_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h180, h190⟩⟩
        exact fixed_func_col_17_190_to_199_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h190, h200⟩⟩
      by_cases h210: n < 210; exact fixed_func_col_17_200_to_209_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h200, h210⟩⟩
      by_cases h220: n < 220; exact fixed_func_col_17_210_to_219_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h210, h220⟩⟩
      by_cases h230: n < 230; exact fixed_func_col_17_220_to_229_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h220, h230⟩⟩
      by_cases h240: n < 240; exact fixed_func_col_17_230_to_239_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h230, h240⟩⟩
      by_cases h250: n < 250; exact fixed_func_col_17_240_to_249_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h240, h250⟩⟩
      exact fixed_func_col_17_250_to_255_output c ⟨n, Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt h250, hn⟩⟩

  lemma fixed_func_col_17_eq_packed_of_lt_usable_rows (c: ValidCircuit P P_Prime) (n: ℕ) (hn: n < c.usable_rows):
    fixed_func_col_17 c n = pack P (into_bits [if n < 256 then n else 0]) := by
      split
      case isTrue h => exact fixed_func_col_17_0_to_256_output c ⟨n, h⟩
      case isFalse h =>
        unfold fixed_func_col_17
        rewrite [
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_neg (by omega),
          if_pos (by omega)
        ]
        simp [pack, keccak_constants, pack_with_base, into_bits, loop_8]

end Keccak.Lookups.PackTable

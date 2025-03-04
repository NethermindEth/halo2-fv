import Examples.Scroll.Keccak.Attributes
import Examples.Scroll.Keccak.Extraction

namespace Keccak
  namespace Env
    @[keccak_constants] def KECCAK_DEGREE: Option ℕ := .some 10
    @[keccak_constants] def KECCAK_ROWS: Option ℕ := .none
  end Env

  @[keccak_constants] def ABSORB_LOOKUP_RANGE: ℕ := 3
  @[keccak_constants] def BIT_COUNT: ℕ := 3
  def BIT_SIZE: ℕ := 2^BIT_COUNT
  @[keccak_constants] def BIT_SIZE_val: BIT_SIZE = 8 := rfl
  @[keccak_constants] def CHI_BASE_LOOKUP_RANGE: ℕ := 5
  @[keccak_constants] def CHI_BASE_LOOKUP_TABLE: (Fin 5) → ℕ
    | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0 | 4 => 0
  @[keccak_constants] def DEFAULT_KECCAK_ROWS: ℕ := 12
  @[keccak_constants] def MAX_DEGREE: ℕ := 9
  @[keccak_constants] def NUM_BITS_PER_WORD: ℕ := 64
  @[keccak_constants] def NUM_BYTES_PER_WORD: ℕ := 8
  @[keccak_constants] def NUM_ROUNDS: ℕ := 24
  @[keccak_constants] def NUM_WORDS_TO_ABSORB: ℕ := 17
  @[keccak_constants] def NUM_WORDS_TO_SQUEEZE: ℕ := 4
  @[keccak_constants] def RHO_MATRIX: Fin 5 → Fin 5 → ℕ
    | 0, 0 => 0  | 1, 0 => 1  | 2, 0 => 62 | 3, 0 => 28 | 4,0 => 27
    | 0, 1 => 36 | 1, 1 => 44 | 2, 1 => 6  | 3, 1 => 55 | 4,1 => 20
    | 0, 2 => 3  | 1, 2 => 10 | 2, 2 => 43 | 3, 2 => 25 | 4,2 => 39
    | 0, 3 => 41 | 1, 3 => 45 | 2, 3 => 15 | 3, 3 => 21 | 4,3 => 8
    | 0, 4 => 18 | 1, 4 => 2  | 2, 4 => 61 | 3, 4 => 56 | 4,4 => 14
  @[keccak_constants] def RHO_PI_LOOKUP_RANGE: ℕ := 4
  @[keccak_constants] def THETA_C_LOOKUP_RANGE: ℕ := 6
end Keccak

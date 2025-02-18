import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  section asserts
    -- NOTE: assert comment says DEFAULT_KECCAK_ROWS > (NUM_BYTES_PER_WORD + 1),
    -- but the assert states the following
    lemma get_num_rows_per_round_assert: DEFAULT_KECCAK_ROWS > NUM_BYTES_PER_WORD := by trivial
  end asserts
end Keccak

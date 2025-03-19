import Mathlib.Tactic.Linarith.Frontend
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  -- get_num_bits_per_lookup is implemented by loop in the rust, so a proof that my rewrite is equivalent
  lemma get_num_bits_per_lookup_correct (range: ℕ) (h_range: range ≥ 2):
    range^(get_num_bits_per_lookup range + 1) + keccak_unusable_rows > 2^get_degree ∧
    range^(get_num_bits_per_lookup range) + keccak_unusable_rows ≤ 2^get_degree := by
      simp_rw [get_num_bits_per_lookup, keccak_constants]
      norm_num
      apply And.intro
      . have h: 965 < range ^ (Nat.log range 965 + 1) := Nat.lt_pow_succ_log_self h_range 965
        linarith
      . simp only [add_tsub_cancel_right, Nat.reduceLeDiff]
        simp [Nat.pow_log_le_self]

end Keccak.Proofs

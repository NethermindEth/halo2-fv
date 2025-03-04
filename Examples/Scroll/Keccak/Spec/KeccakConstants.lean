import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  @[keccak_constants] lemma get_degree_val: get_degree = 10 := rfl

  @[keccak_constants] lemma get_num_bits_per_absorb_lookup_val: get_num_bits_per_absorb_lookup = 6 := by
    rewrite [get_num_bits_per_absorb_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_base_chi_lookup_val: get_num_bits_per_base_chi_lookup = 4 := by
    rewrite [get_num_bits_per_base_chi_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_lookup_val: get_num_bits_per_base_chi_lookup = 4 := by
    rewrite [get_num_bits_per_base_chi_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_theta_c_lookup_val: get_num_bits_per_theta_c_lookup = 3 := by
    rewrite [get_num_bits_per_theta_c_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_rows_per_round_val: get_num_rows_per_round = 12 := rfl

  @[keccak_constants] lemma keccak_unusable_rows_val: keccak_unusable_rows = 59 := rfl

  @[keccak_constants] lemma part_size_c_val: part_size_c = 3 := by simp [part_size_c, get_num_bits_per_theta_c_lookup_val]

  @[keccak_constants] lemma rho_by_pi_num_word_parts_val: rho_by_pi_num_word_parts = 16 := by
    simp [rho_by_pi_num_word_parts, rho_by_pi_target_word_sizes, rho_by_pi_part_size, get_num_bits_per_base_chi_lookup_val, target_part_sizes, NUM_BITS_PER_WORD]
    rfl
end Keccak

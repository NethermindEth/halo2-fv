import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  @[keccak_constants] lemma get_num_bits_per_absorb_lookup_val: get_num_bits_per_absorb_lookup = 6 := by
    rewrite [get_num_bits_per_absorb_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_base_chi_lookup_val: get_num_bits_per_base_chi_lookup = 4 := by
    rewrite [get_num_bits_per_base_chi_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma get_num_bits_per_theta_c_lookup_val: get_num_bits_per_theta_c_lookup = 3 := by
    rewrite [get_num_bits_per_theta_c_lookup, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  @[keccak_constants] lemma rho_by_pi_num_word_parts_val : rho_by_pi_num_word_parts = 16 := by
    simp [rho_by_pi_num_word_parts, get_num_bits_per_base_chi_lookup_val, target_part_sizes, List.length]
end Keccak

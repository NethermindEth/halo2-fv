import Examples.Scroll.Keccak.Spec

namespace Keccak

  namespace Gates

    namespace SplitUniform

      lemma row_range (h: 299 < n) (h': round ≤ 23): 12*(round+1) + 11 < n := by linarith

      lemma gate_33_34_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_33 c) (hsplit_gate: gate_34 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 3 4)
          (cell_offset := 1616)
          (rot := RHO_MATRIX 0 3)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 0 3)
        := by
          unfold gate_33 at hrot_gate
          unfold gate_34 at hsplit_gate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hrot_gate hsplit_gate
          replace hrot_gate := hrot_gate (12*(round+1))
          replace hsplit_gate := hsplit_gate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hrot_gate hsplit_gate
          replace hrot_gate := eq_neg_of_add_eq_zero_left hrot_gate
          replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
          rewrite [neg_involutive] at hrot_gate hsplit_gate
          have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
          simp [to_cell_manager, h_row_range, to_decode, to_os] at hrot_gate hsplit_gate
          rewrite [get_num_bits_per_base_chi_lookup_val, RHO_MATRIX]
          unfold SplitUniform.constraint
          apply And.intro
          . rewrite [←hsplit_gate]
            congr
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, List.rotateRight]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [List.rotateRight]
            aesop
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps]
            rewrite [Fin.coe_ofNat_eq_mod, Fin.coe_ofNat_eq_mod]
            simp
            rewrite [←hrot_gate]
            simp [mul_comm]

      lemma gate_35_36_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_35 c) (hsplit_gate: gate_36 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 3 1)
          (cell_offset := 1618)
          (rot := RHO_MATRIX 1 3)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 1 3)
        := by
          unfold gate_35 at hrot_gate
          unfold gate_36 at hsplit_gate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hrot_gate hsplit_gate
          replace hrot_gate := hrot_gate (12*(round+1))
          replace hsplit_gate := hsplit_gate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hrot_gate hsplit_gate
          replace hrot_gate := eq_neg_of_add_eq_zero_left hrot_gate
          replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
          rewrite [neg_involutive] at hrot_gate hsplit_gate
          have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
          simp [to_cell_manager, h_row_range, to_decode, to_os] at hrot_gate hsplit_gate
          rewrite [get_num_bits_per_base_chi_lookup_val, RHO_MATRIX]
          unfold SplitUniform.constraint
          apply And.intro
          . rewrite [←hsplit_gate]
            congr
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, List.rotateRight]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [List.rotateRight]
            aesop
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps]
            rewrite [Fin.coe_ofNat_eq_mod]
            simp
            rewrite [←hrot_gate]
            simp [mul_comm]

      lemma gate_37_38_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_37 c) (hsplit_gate: gate_38 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 3 3)
          (cell_offset := 1620)
          (rot := RHO_MATRIX 2 3)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 2 3)
        := by
          unfold gate_37 at hrot_gate
          unfold gate_38 at hsplit_gate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hrot_gate hsplit_gate
          replace hrot_gate := hrot_gate (12*(round+1))
          replace hsplit_gate := hsplit_gate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hrot_gate hsplit_gate
          replace hrot_gate := eq_neg_of_add_eq_zero_left hrot_gate
          replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
          rewrite [neg_involutive] at hrot_gate hsplit_gate
          have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
          simp [to_cell_manager, h_row_range, to_decode, to_os] at hrot_gate hsplit_gate
          rewrite [get_num_bits_per_base_chi_lookup_val, RHO_MATRIX]
          unfold SplitUniform.constraint
          apply And.intro
          . rewrite [←hsplit_gate]
            congr
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, List.rotateRight]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [List.rotateRight]
            aesop
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps]
            rewrite [Fin.coe_ofNat_eq_mod]
            simp
            rewrite [←hrot_gate]
            simp [mul_comm]

      lemma gate_39_40_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_39 c) (hsplit_gate: gate_40 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 3 0)
          (cell_offset := 1622)
          (rot := RHO_MATRIX 3 3)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 3 3)
        := by
          unfold gate_39 at hrot_gate
          unfold gate_40 at hsplit_gate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hrot_gate hsplit_gate
          replace hrot_gate := hrot_gate (12*(round+1))
          replace hsplit_gate := hsplit_gate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hrot_gate hsplit_gate
          replace hrot_gate := eq_neg_of_add_eq_zero_left hrot_gate
          replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
          rewrite [neg_involutive] at hrot_gate hsplit_gate
          have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
          simp [to_cell_manager, h_row_range, to_decode, to_os] at hrot_gate hsplit_gate
          rewrite [get_num_bits_per_base_chi_lookup_val, RHO_MATRIX]
          unfold SplitUniform.constraint
          apply And.intro
          . rewrite [←hsplit_gate]
            congr
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, List.rotateRight]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [List.rotateRight]
            aesop
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps]
            rewrite [Fin.coe_ofNat_eq_mod]
            simp
            rewrite [←hrot_gate]
            simp [mul_comm]

      lemma gate_41_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_41 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 3 2)
          (cell_offset := 1624)
          (rot := RHO_MATRIX 4 3)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 4 3)
        := by
          unfold gate_41 at hsplit_gate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hsplit_gate
          replace hsplit_gate := hsplit_gate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hsplit_gate
          replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
          rewrite [neg_involutive] at hsplit_gate
          have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
          simp [to_cell_manager, h_row_range, to_decode, to_os] at hsplit_gate
          rewrite [get_num_bits_per_base_chi_lookup_val, RHO_MATRIX]
          unfold SplitUniform.constraint
          apply And.intro
          . rewrite [←hsplit_gate]
            congr
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants, List.rotateRight]
            aesop
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts]
    end SplitUniform
  end Gates
end Keccak

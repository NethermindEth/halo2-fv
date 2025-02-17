import Examples.Scroll.Keccak.Spec

namespace Keccak

  namespace Gates

    namespace SplitUniform

      lemma row_range (h: 299 < n) (h': round ≤ 23): 12*(round+1) + 11 < n := by linarith

      lemma gate_42_43_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_42 c) (hsplit_gate: gate_43 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 4 2)
          (cell_offset := 1624)
          (rot := RHO_MATRIX 0 4)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 0 4)
        := by
          unfold gate_42 at hrot_gate
          unfold gate_43 at hsplit_gate
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

      lemma gate_44_aux (c: ValidCircuit P P_Prime) (hrot_gate: gate_44 c) (h_fixed: c.1.Fixed = fixed_func c) (h_n: 299 < c.n) :
        ∀ round ≤ 23,
        cell_manager c round 1626 + 64 * cell_manager c round 1627 = cell_manager c round 688
      := by
        unfold gate_44 at hrot_gate
        intro round h_round_range
        simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hrot_gate
        replace hrot_gate := hrot_gate (12*(round+1))
        rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hrot_gate
        replace hrot_gate := eq_neg_of_add_eq_zero_left hrot_gate
        rewrite [neg_involutive] at hrot_gate
        have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
        simp [to_cell_manager, h_row_range, to_decode, to_os] at hrot_gate
        assumption

      lemma gate_45_aux (c: ValidCircuit P P_Prime) (hsplit_gate: gate_45 c) (h_fixed: c.1.Fixed = fixed_func c) (h_n: 299 < c.n) :
        ∀ round ≤ 23,
        Decode.expr
          [(2, cell_manager c round 1627), (4, cell_manager c round 689), (4, cell_manager c round 690),
            (4, cell_manager c round 691), (4, cell_manager c round 692), (4, cell_manager c round 693),
            (4, cell_manager c round 694), (4, cell_manager c round 695), (4, cell_manager c round 744),
            (4, cell_manager c round 745), (4, cell_manager c round 746), (4, cell_manager c round 747),
            (4, cell_manager c round 748), (4, cell_manager c round 749), (4, cell_manager c round 750),
            (4, cell_manager c round 751), (2, cell_manager c round 1626)] =
        os c round 1 4
      := by
        unfold gate_45 at hsplit_gate
        intro round h_round_range
        simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hsplit_gate
        replace hsplit_gate := hsplit_gate (12*(round+1))
        rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hsplit_gate
        replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
        rewrite [neg_involutive] at hsplit_gate
        have h_row_range : (12*(round+1)) + 11 < c.n := row_range h_n h_round_range
        simp [to_cell_manager, h_row_range, to_decode, to_os] at hsplit_gate
        assumption

      lemma gate_44_45_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_44 c) (hsplit_gate: gate_45 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 4 4)
          (cell_offset := 1626)
          (rot := RHO_MATRIX 1 4)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 1 4)
        := by
          intro round h_round_range
          replace hrot_gate := gate_44_aux c hrot_gate h_fixed h_n round h_round_range
          replace hsplit_gate := gate_45_aux c hsplit_gate h_fixed h_n round h_round_range
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

      lemma gate_46_47_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_46 c) (hsplit_gate: gate_47 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 4 1)
          (cell_offset := 1628)
          (rot := RHO_MATRIX 2 4)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 2 4)
        := by
          unfold gate_46 at hrot_gate
          unfold gate_47 at hsplit_gate
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

      lemma gate_48_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_48 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 4 3)
          (cell_offset := 1630)
          (rot := RHO_MATRIX 3 4)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 3 4)
        := by
          unfold gate_48 at hsplit_gate
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

      lemma gate_49_50_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_49 c) (hsplit_gate: gate_50 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 4 0)
          (cell_offset := 1630)
          (rot := RHO_MATRIX 4 4)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 4 4)
        := by
          unfold gate_49 at hrot_gate
          unfold gate_50 at hsplit_gate
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

    end SplitUniform

  end Gates

end Keccak

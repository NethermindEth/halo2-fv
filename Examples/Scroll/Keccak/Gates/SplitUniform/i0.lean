import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.Decode
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Os

namespace Keccak

  namespace Gates

    namespace SplitUniform

      lemma row_range (h: 299 < n) (h': round ≤ 23): 12*(round+1) + 11 < n := by linarith

      lemma gate_8_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_8 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 0 0)
          (cell_offset := 1596)
          (rot := RHO_MATRIX 0 0)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 0 0)
        := by
          unfold gate_8 at hsplit_gate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hsplit_gate
          replace hsplit_gate := hsplit_gate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hsplit_gate
          replace hsplit_gate := eq_neg_of_add_eq_zero_left hsplit_gate
          rewrite [neg_involutive] at hsplit_gate
          have h_row_range : (12*(round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range, to_decode, to_os] at hsplit_gate
          rewrite [get_num_bits_per_base_chi_lookup_val, RHO_MATRIX]
          unfold SplitUniform.constraint
          apply And.intro
          . rewrite [←hsplit_gate]
            congr
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants]
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts]

      lemma gate_9_10_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_9 c) (hsplit_gate: gate_10 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 0 2)
          (cell_offset := 1596)
          (rot := RHO_MATRIX 1 0)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 1 0)
        := by
          unfold gate_9 at hrot_gate
          unfold gate_10 at hsplit_gate
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
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps]
            rewrite [←hrot_gate]
            simp [mul_comm]

      lemma gate_11_12_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_11 c) (hsplit_gate: gate_12 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 0 4)
          (cell_offset := 1598)
          (rot := RHO_MATRIX 2 0)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 2 0)
        := by
          unfold gate_11 at hrot_gate
          unfold gate_12 at hsplit_gate
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

      lemma gate_13_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_13 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 0 1)
          (cell_offset := 1600)
          (rot := RHO_MATRIX 3 0)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 3 0)
        := by
          unfold gate_13 at hsplit_gate
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
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts]


      lemma gate_14_15_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_14 c) (hsplit_gate: gate_15 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 0 3)
          (cell_offset := 1600)
          (rot := RHO_MATRIX 4 0)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 4 0)
        := by
          unfold gate_14 at hrot_gate
          unfold gate_15 at hsplit_gate
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

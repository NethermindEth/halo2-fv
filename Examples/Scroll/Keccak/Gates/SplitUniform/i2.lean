import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.Decode
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Os

namespace Keccak

  namespace Gates

    namespace SplitUniform

      lemma row_range (h: 299 < n) (h': round ≤ 23): 12*(round+1) + 11 < n := by linarith

      lemma gate_23_24_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_23 c) (hsplit_gate: gate_24 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 2 1)
          (cell_offset := 1606)
          (rot := RHO_MATRIX 0 2)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 0 2)
        := by
          unfold gate_23 at hrot_gate
          unfold gate_24 at hsplit_gate
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

      lemma gate_25_26_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_25 c) (hsplit_gate: gate_26 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 2 3)
          (cell_offset := 1608)
          (rot := RHO_MATRIX 1 2)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 1 2)
        := by
          unfold gate_25 at hrot_gate
          unfold gate_26 at hsplit_gate
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

      lemma gate_27_28_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_27 c) (hsplit_gate: gate_28 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 2 0)
          (cell_offset := 1610)
          (rot := RHO_MATRIX 2 2)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 2 2)
        := by
          unfold gate_27 at hrot_gate
          unfold gate_28 at hsplit_gate
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

      lemma gate_29_30_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_29 c) (hsplit_gate: gate_30 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 2 2)
          (cell_offset := 1612)
          (rot := RHO_MATRIX 3 2)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 3 2)
        := by
          unfold gate_29 at hrot_gate
          unfold gate_30 at hsplit_gate
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

      lemma gate_31_32_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_31 c) (hsplit_gate: gate_32 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c round
          (output_cells := rho_pi_chi_cells c round 0 2 4)
          (cell_offset := 1614)
          (rot := RHO_MATRIX 4 2)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c round 4 2)
        := by
          unfold gate_31 at hrot_gate
          unfold gate_32 at hsplit_gate
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

import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.Decode
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Os.All

namespace Keccak

  namespace Gates

    namespace SplitUniform

      lemma row_range (h: 299 < n) (h': round ≤ 23): 12*(round+1) + 11 < n := by omega

      lemma gate_16_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_16 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c (round+1)
          (output_cells := rho_pi_chi_cells c (round+1) 0 1 3)
          (cell_offset := 1600)
          (rot := RHO_MATRIX 0 1)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c (round+1) 0 1)
        := by
          unfold gate_16 at hsplit_gate
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
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants, list_ops]
            aesop
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, list_ops]

      lemma gate_17_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_17 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c (round+1)
          (output_cells := rho_pi_chi_cells c (round+1) 0 1 0)
          (cell_offset := 1600)
          (rot := RHO_MATRIX 1 1)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c (round+1) 1 1)
        := by
          unfold gate_17 at hsplit_gate
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
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants, list_ops]
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, list_ops]

      lemma gate_18_19_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_18 c) (hsplit_gate: gate_19 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c (round+1)
          (output_cells := rho_pi_chi_cells c (round+1) 0 1 2)
          (cell_offset := 1602)
          (rot := RHO_MATRIX 2 1)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c (round+1) 2 1)
        := by
          unfold gate_18 at hrot_gate
          unfold gate_19 at hsplit_gate
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
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, list_ops]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [list_ops, fin_vals]
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps, list_ops]
            rewrite [←hrot_gate]
            rw [mul_comm]

      lemma gate_20_21_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hrot_gate: gate_20 c) (hsplit_gate: gate_21 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c (round+1)
          (output_cells := rho_pi_chi_cells c (round+1) 0 1 4)
          (cell_offset := 1604)
          (rot := RHO_MATRIX 3 1)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c (round+1) 3 1)
        := by
          unfold gate_20 at hrot_gate
          unfold gate_21 at hsplit_gate
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
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, list_ops]
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants, fin_vals]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [list_ops]
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, rho_pi_chi_cells, zmod_pow_simps, list_ops]
            rewrite [Fin.coe_ofNat_eq_mod]
            simp
            rewrite [←hrot_gate]
            simp [mul_comm]

      lemma gate_22_split_uniform (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hsplit_gate: gate_22 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        SplitUniform.constraint c (round+1)
          (output_cells := rho_pi_chi_cells c (round+1) 0 1 1)
          (cell_offset := 1606)
          (rot := RHO_MATRIX 4 1)
          (target_part_size := get_num_bits_per_base_chi_lookup)
          (input := os c (round+1) 4 1)
        := by
          unfold gate_22 at hsplit_gate
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
            simp [get_rotate_count, word_parts_known, target_part_sizes_known, rho_by_pi_num_word_parts_val, list_ops]
            apply list_rotateLeft_eq_of_eq_rotateRight
            simp [SplitUniform.input_parts, rho_pi_chi_cells, keccak_constants, list_ops, fin_vals]
          . simp [keccak_constants, word_parts_known, get_rotate_count, target_part_sizes_known, SplitUniform.rot_parts, list_ops]
    end SplitUniform
  end Gates
end Keccak

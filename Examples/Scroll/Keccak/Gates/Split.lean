import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak

  namespace Gates

    namespace Split

      lemma gate_0_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_0 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 36)
          (rot := 0)
          (target_part_size := get_num_bits_per_absorb_lookup)
          (input := input c round)
        := by
          unfold gate_0 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_2_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_2 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 60)
          (rot := 0)
          (target_part_size := NUM_BYTES_PER_WORD)
          (input := absorb_data c round)
        := by
          unfold gate_2 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_3_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_3 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 96)
          (rot := 0)
          (target_part_size := get_num_bits_per_theta_c_lookup)
          (input := s c round 0 0 + s c round 0 1 + s c round 0 2 + s c round 0 3 + s c round 0 4)
        := by
          unfold gate_3 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_4_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_4 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 118)
          (rot := 0)
          (target_part_size := get_num_bits_per_theta_c_lookup)
          (input := s c round 1 0 + s c round 1 1 + s c round 1 2 + s c round 1 3 + s c round 1 4)
        := by
          unfold gate_4 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_5_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_5 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 140)
          (rot := 0)
          (target_part_size := get_num_bits_per_theta_c_lookup)
          (input := s c round 2 0 + s c round 2 1 + s c round 2 2 + s c round 2 3 + s c round 2 4)
        := by
          unfold gate_5 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_6_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_6 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 162)
          (rot := 0)
          (target_part_size := get_num_bits_per_theta_c_lookup)
          (input := s c round 3 0 + s c round 3 1 + s c round 3 2 + s c round 3 3 + s c round 3 4)
        := by
          unfold gate_6 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_7_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_7 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 184)
          (rot := 0)
          (target_part_size := get_num_bits_per_theta_c_lookup)
          (input := s c round 4 0 + s c round 4 1 + s c round 4 2 + s c round 4 3 + s c round 4 4)
        := by
          unfold gate_7 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

      lemma gate_51_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_51 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 1632)
          (rot := 0)
          (target_part_size := get_num_bits_per_absorb_lookup)
          (input :=
            Decode.expr [ -- chi_os[0][0]
              (4, c.get_advice_wrapped 105 (12*(round+1)) 0),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 1),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 2),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 3),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 4),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 5),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 6),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 7),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 8),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 9),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 10),
              (4, c.get_advice_wrapped 105 (12*(round+1)) 11),
              (4, c.get_advice_wrapped 110 (12*(round+1)) 0),
              (4, c.get_advice_wrapped 110 (12*(round+1)) 1),
              (4, c.get_advice_wrapped 110 (12*(round+1)) 2),
              (4, c.get_advice_wrapped 110 (12*(round+1)) 3)
            ] + round_cst c (12*(round+1))
          )
        := by
          unfold gate_51 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          simp [to_cell_manager, h_row_range, round_cst, h_fixed, ValidCircuit.get_fixed]

      lemma gate_77_split (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_77 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 1668)
          (rot := 0)
          (target_part_size := 8)
          (input := squeeze_from c round)
        := by
          unfold gate_77 at hgate
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate
          replace hgate := hgate (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate
          replace hgate := eq_neg_of_add_eq_zero_left hgate
          rewrite [neg_involutive] at hgate
          have h_row_range : (12 * (round+1)) + 11 < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate
          simp [Split.constraint, keccak_constants, Split.expr, word_parts_known, List.enum, Decode.expr, zmod_pow_simps]
          rewrite [hgate]
          rfl

    end Split

  end Gates

end Keccak

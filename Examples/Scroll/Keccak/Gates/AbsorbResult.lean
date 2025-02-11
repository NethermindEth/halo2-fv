import Examples.Scroll.Keccak.Spec

namespace Keccak

  namespace Gates

    namespace AbsorbResult

      lemma gate_1_absorb_result (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate_1: gate_1 c) (h_n: 299 < c.n):
        ∀ round ≤ 23,
        Split.constraint c round
          (cell_offset := 48)
          (rot := 0)
          (target_part_size := get_num_bits_per_absorb_lookup)
          (input := absorb_result c round)
        := by
          unfold gate_1 at hgate_1
          intro round h_round_range
          simp only [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_2_q_round] at hgate_1
          replace hgate_1 := hgate_1 (12*(round+1))
          rewrite [Selectors.q_round_at_round_start c h_round_range, one_mul] at hgate_1
          replace hgate_1 := eq_neg_of_add_eq_zero_left hgate_1
          rewrite [neg_involutive] at hgate_1
          have h_row_range : (12*(round+1)+11) < c.n := by linarith
          simp [to_cell_manager, h_row_range] at hgate_1
          simp [Split.constraint, get_num_bits_per_absorb_lookup_val, Split.expr, WordParts.new_6_0_false, List.enum, Decode.expr, BIT_COUNT, zmod_pow_simps]
          rewrite [hgate_1]
          rfl

    end AbsorbResult

  end Gates

end Keccak

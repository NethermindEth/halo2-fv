import Examples.Scroll.Keccak.Gates.Split
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

    lemma packed_parts_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24,
      (packed_parts c round).2
    := by
      intro round h_round
      replace h_round := Finset.mem_Icc.mp h_round
      unfold packed_parts Split.expr
      have h_gate_2 := gate_2_of_meets_constraints h
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      convert Gates.Split.gate_2_split c h_fixed h_gate_2 (by omega) (round-1) (by omega) <;> omega

  lemma input_bytes_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24,
      (input_bytes c round).2
    := by
      intro round h_round
      unfold input_bytes Transform.split_expr
      simp [packed_parts]
      split_ands
      . congr
        have := packed_parts_of_meets_constraints h round h_round
        unfold packed_parts Split.expr at this
        simp_all
      . rfl
      . simp [keccak_constants, Split.expr, Split.expr_res, word_parts_known, List.enum]
        intro num_bits_in cell_in num_bits_out cell_out h_mem
        have h_lookup_1 := lookup_1_of_meets_constraints h
        have h_fixed := fixed_of_meets_constraints h
        have h_usable_rows := usable_rows_range_of_meets_constraints h
        have h_n := n_range_of_meets_constraints h
        have h_lookup_1 := Lookups.PackTable.lookup_1_pack_table c h_lookup_1 h_fixed
        replace h_round := (Finset.mem_Icc.mp h_round).2
        have : ∀ offset < 11, ∃ lookup_row,
          Lookups.PackTable.transform_table _ lookup_row =
          (c.get_advice 12 (12 * round + offset), c.get_advice 13 (12 * round + offset))
          := by
            intro offset hoffset
            specialize h_lookup_1 (12 * round + offset) (by omega)
            obtain ⟨x0, h_x0, h_input, h_output⟩ := h_lookup_1
            rewrite [h_input, h_output]
            use x0
            unfold Lookups.PackTable.transform_table
            rw [if_pos (by omega)]
        rcases h_mem with
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩
        all_goals (
          subst h_cell_in h_cell_out
          simp [cell_manager_to_raw]
          rewrite [Nat.mod_eq_of_lt (by omega)]
        )
        . exact this 0 (by trivial)
        all_goals refine this ?_ ?_ ; trivial

end Keccak.Proofs

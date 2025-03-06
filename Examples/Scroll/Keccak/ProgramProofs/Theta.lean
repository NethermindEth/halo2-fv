import Examples.Scroll.Keccak.Gates.Split
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma c_parts_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24, ∀ idx,
      (c_parts c round idx).2
    := by
      intro round h_round idx
      replace h_round := Finset.mem_Icc.mp h_round
      unfold c_parts Split.expr
      have h_gate_3 := gate_3_of_meets_constraints h
      have h_gate_4 := gate_4_of_meets_constraints h
      have h_gate_5 := gate_5_of_meets_constraints h
      have h_gate_6 := gate_6_of_meets_constraints h
      have h_gate_7 := gate_7_of_meets_constraints h
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      fin_cases idx
      . convert Gates.Split.gate_3_split c h_fixed h_gate_3 (by omega) (round-1) (by omega) <;> omega
      . convert Gates.Split.gate_4_split c h_fixed h_gate_4 (by omega) (round-1) (by omega) <;> omega
      . convert Gates.Split.gate_5_split c h_fixed h_gate_5 (by omega) (round-1) (by omega) <;> omega
      . convert Gates.Split.gate_6_split c h_fixed h_gate_6 (by omega) (round-1) (by omega) <;> omega
      . convert Gates.Split.gate_7_split c h_fixed h_gate_7 (by omega) (round-1) (by omega) <;> omega

  lemma bc_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24, ∀ idx,
      (bc c round idx).2
    := by
      intro round h_round idx
      unfold bc Transform.split_expr
      simp
      split_ands
      . congr
        have := c_parts_of_meets_constraints h round h_round
        unfold c_parts Split.expr at this
        simp_all
      . decide
      . simp [c_parts, keccak_constants, Split.expr, Split.expr_res, word_parts_known, List.enum]
        intro num_bits_in cell_in num_bits_out cell_out h_mem
        have h_usable_rows := usable_rows_range_of_meets_constraints h
        have h_n := n_range_of_meets_constraints h
        have h_lookups := Lookups.Normalize_6.lookup_2_to_11_normalize_6 c
          (lookup_2_of_meets_constraints h)
          (lookup_3_of_meets_constraints h)
          (lookup_4_of_meets_constraints h)
          (lookup_5_of_meets_constraints h)
          (lookup_6_of_meets_constraints h)
          (lookup_7_of_meets_constraints h)
          (lookup_8_of_meets_constraints h)
          (lookup_9_of_meets_constraints h)
          (lookup_10_of_meets_constraints h)
          (lookup_11_of_meets_constraints h)
          (fixed_of_meets_constraints h)
        replace h_lookups : ∀ col ≤ 24, col ≥ 15 → ∀ row < c.usable_rows, ∃ x,
          Lookups.Normalize_6.transform_table _ x =
          (c.get_advice col row, c.get_advice (col+10) row)
        := by
          intro col h_col_le h_col_ge row h_row
          specialize h_lookups col (Finset.mem_Icc.mpr ⟨h_col_ge, h_col_le⟩) row h_row
          obtain ⟨x0, x1, x2, h_x0, h_x1, h_x2, h_in, h_out⟩ := h_lookups
          use x2 + 6*x1 + 36*x0
          rewrite [h_in, h_out, Lookups.Normalize_6.transform_table, Lookups.Normalize_6.input_by_row, Lookups.Normalize_6.output_by_row]
          rewrite [if_pos (by omega)]
          simp
          split_ands
          . congr <;> omega
          . congr <;> omega
        replace h_round := (Finset.mem_Icc.mp h_round).2
        rcases h_mem with
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
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
          rewrite [Nat.mod_eq_of_lt (by omega), @Nat.mod_eq_of_lt _ c.n (by omega)]
          convert h_lookups _ _ _ _ _ using 5 <;> omega
        )

end Keccak.Proofs

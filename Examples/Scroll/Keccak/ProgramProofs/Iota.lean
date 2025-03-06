import Examples.Scroll.Keccak.Gates.NextRowCheck.All
import Examples.Scroll.Keccak.Gates.Split
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs
  lemma iota_parts_of_meets_constraints (h: meets_constraints c):
    ∀ round : Finset.Icc 1 24,
      (iota_parts c round).2
    := by
      intro round
      simp [iota_parts, keccak_constants, Split.expr]
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      obtain ⟨round, h_round⟩ := round
      replace h_round := Finset.mem_Icc.mp h_round
      have h_gate := Gates.Split.gate_51_split c h_fixed (gate_51_of_meets_constraints h) (by omega) (round-1) (by omega)
      convert h_gate
      . dsimp; omega
      . simp [keccak_constants]
      . dsimp [iota_input]; congr <;> omega

  lemma iota_s_0_0_transform_of_meets_constraints (h: meets_constraints c):
    ∀ round : Finset.Icc 1 24,
      (iota_s_0_0_transform c round).2
    := by
      intro round
      simp [iota_s_0_0_transform, Transform.split_expr]
      split_ands
      . have := iota_parts_of_meets_constraints h round
        simp_all [iota_parts, Split.expr]
      . simp [keccak_constants]
      . intro num_bits_in cell_in num_bits_out cell_out h_mem
        simp [iota_parts, Split.expr, Split.expr_res, word_parts_known, keccak_constants, List.enum] at h_mem
        simp [cell_manager_to_col_row, cell_manager_column] at h_mem
        have h_fixed := fixed_of_meets_constraints h
        have h_lookup := Lookups.Normalize_3.lookup_85_normalize_3 c (lookup_85_of_meets_constraints h) h_fixed
        have h_usable_rows := usable_rows_range_of_meets_constraints h
        have h_n := n_range_of_meets_constraints h
        have h_goal: ∀ row < c.usable_rows,
          ∃ lookup_row, Lookups.Normalize_3.transform_table _ lookup_row = (c.get_advice 143 row, c.get_advice 144 row)
        := by
          intro row h_row
          specialize h_lookup row h_row
          obtain ⟨x0, x1, x2, x3, x4, x5, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_in, h_out⟩ := h_lookup
          use x5 + 3*x4 + 9*x3 + 27*x2 + 81*x1 + 243*x0
          simp [Lookups.Normalize_3.transform_table]
          rewrite [if_pos (by omega), h_in, h_out]
          dsimp [Lookups.Normalize_3.input_by_row, Lookups.Normalize_3.output_by_row]
          congr <;> omega
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
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩
        all_goals {
          subst h_cell_in h_cell_out
          simp [cell_manager_row]
          apply h_goal
          obtain ⟨round, h_round⟩ := round
          replace h_round := Finset.mem_Icc.mp h_round
          dsimp
          rewrite [Nat.mod_eq_of_lt] <;> omega
        }

  lemma next_row_check_of_meets_constraints (h: meets_constraints c) :
    ∀ round: Finset.Icc 1 24, ∀ i j,
      next_row_check c round i j
    := by
      intro round i j
      simp [next_row_check]
      obtain ⟨round, h_round⟩ := round
      replace h_round := Finset.mem_Icc.mp h_round
      dsimp
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      fin_cases i <;> fin_cases j
      . convert Gates.NextRowCheck.gate_52_next_row_check c h_fixed (gate_52_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_53_next_row_check c h_fixed (gate_53_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_54_next_row_check c h_fixed (gate_54_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_55_next_row_check c h_fixed (gate_55_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_56_next_row_check c h_fixed (gate_56_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_57_next_row_check c h_fixed (gate_57_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_58_next_row_check c h_fixed (gate_58_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_59_next_row_check c h_fixed (gate_59_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_60_next_row_check c h_fixed (gate_60_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_61_next_row_check c h_fixed (gate_61_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_62_next_row_check c h_fixed (gate_62_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_63_next_row_check c h_fixed (gate_63_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_64_next_row_check c h_fixed (gate_64_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_65_next_row_check c h_fixed (gate_65_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_66_next_row_check c h_fixed (gate_66_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_67_next_row_check c h_fixed (gate_67_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_68_next_row_check c h_fixed (gate_68_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_69_next_row_check c h_fixed (gate_69_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_70_next_row_check c h_fixed (gate_70_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_71_next_row_check c h_fixed (gate_71_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_72_next_row_check c h_fixed (gate_72_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_73_next_row_check c h_fixed (gate_73_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_74_next_row_check c h_fixed (gate_74_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_75_next_row_check c h_fixed (gate_75_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega
      . convert Gates.NextRowCheck.gate_76_next_row_check c h_fixed (gate_76_of_meets_constraints h) (by omega) (round-1) (by omega) using 2 <;> omega





end Keccak.Proofs

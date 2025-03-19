import Examples.Scroll.Keccak.Gates.SplitUniform.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.RhoPiChiCells

namespace Keccak.Proofs

  lemma num_rho_pi_chi_columns_correct:
    (rho_pi_chi_column 2 4 4 rho_by_pi_num_word_parts + 1 -
    rho_pi_chi_column 2 0 0 0) / 5 =
    num_rho_pi_chi_columns
  := by
    unfold num_rho_pi_chi_columns
    simp [keccak_constants, rho_pi_chi_column]
    rewrite [Fin.coe_ofNat_eq_mod, Fin.coe_ofNat_eq_mod]
    simp [keccak_constants]

  lemma s_parts_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24, ∀ i j,
      (s_parts c round i j).2
    := by
      intro round h_round i j
      replace h_round := Finset.mem_Icc.mp h_round
      simp [s_parts, SplitUniform.expr]
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      fin_cases j <;> fin_cases i <;> dsimp
      . convert Gates.SplitUniform.gate_8_split_uniform c h_fixed (gate_8_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_9_10_split_uniform c h_fixed (gate_9_of_meets_constraints h) (gate_10_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_11_12_split_uniform c h_fixed (gate_11_of_meets_constraints h) (gate_12_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_13_split_uniform c h_fixed (gate_13_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_14_15_split_uniform c h_fixed (gate_14_of_meets_constraints h) (gate_15_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_16_split_uniform c h_fixed (gate_16_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_17_split_uniform c h_fixed (gate_17_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_18_19_split_uniform c h_fixed (gate_18_of_meets_constraints h) (gate_19_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_20_21_split_uniform c h_fixed (gate_20_of_meets_constraints h) (gate_21_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_22_split_uniform c h_fixed (gate_22_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_23_24_split_uniform c h_fixed (gate_23_of_meets_constraints h) (gate_24_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_25_26_split_uniform c h_fixed (gate_25_of_meets_constraints h) (gate_26_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_27_28_split_uniform c h_fixed (gate_27_of_meets_constraints h) (gate_28_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_29_30_split_uniform c h_fixed (gate_29_of_meets_constraints h) (gate_30_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_31_32_split_uniform c h_fixed (gate_31_of_meets_constraints h) (gate_32_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_33_34_split_uniform c h_fixed (gate_33_of_meets_constraints h) (gate_34_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_35_36_split_uniform c h_fixed (gate_35_of_meets_constraints h) (gate_36_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_37_38_split_uniform c h_fixed (gate_37_of_meets_constraints h) (gate_38_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_39_40_split_uniform c h_fixed (gate_39_of_meets_constraints h) (gate_40_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_41_split_uniform c h_fixed (gate_41_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_42_43_split_uniform c h_fixed (gate_42_of_meets_constraints h) (gate_43_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_44_45_split_uniform c h_fixed (gate_44_of_meets_constraints h) (gate_45_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_46_47_split_uniform c h_fixed (gate_46_of_meets_constraints h) (gate_47_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_48_split_uniform c h_fixed (gate_48_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega
      . convert Gates.SplitUniform.gate_49_50_split_uniform c h_fixed (gate_49_of_meets_constraints h) (gate_50_of_meets_constraints h) (by omega) (round - 1) (by omega) <;> omega

  lemma s_parts'_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24, ∀ i j,
      (s_parts' c round i j).2
    := by
      intro round h_round i j
      replace h_round := Finset.mem_Icc.mp h_round
      simp [s_parts', TransformTo.expr]
      split_ands
      . simp [s_parts, SplitUniform.expr, SplitUniform.expr_res, keccak_constants, target_part_sizes_known, list_ops]
        simp [SplitUniform.output_parts]
      . intro num_bits cell_in cell_out h_mem
        simp [s_parts, keccak_constants, SplitUniform.expr, SplitUniform.expr_res, target_part_sizes_known, list_ops] at h_mem
        simp [SplitUniform.output_parts] at h_mem
        have h_lookups := Lookups.Normalize_4.lookup_12_to_46_normalize_4 c
          (lookup_12_of_meets_constraints h)
          (lookup_13_of_meets_constraints h)
          (lookup_14_of_meets_constraints h)
          (lookup_15_of_meets_constraints h)
          (lookup_16_of_meets_constraints h)
          (lookup_17_of_meets_constraints h)
          (lookup_18_of_meets_constraints h)
          (lookup_19_of_meets_constraints h)
          (lookup_20_of_meets_constraints h)
          (lookup_21_of_meets_constraints h)
          (lookup_22_of_meets_constraints h)
          (lookup_23_of_meets_constraints h)
          (lookup_24_of_meets_constraints h)
          (lookup_25_of_meets_constraints h)
          (lookup_26_of_meets_constraints h)
          (lookup_27_of_meets_constraints h)
          (lookup_28_of_meets_constraints h)
          (lookup_29_of_meets_constraints h)
          (lookup_30_of_meets_constraints h)
          (lookup_31_of_meets_constraints h)
          (lookup_32_of_meets_constraints h)
          (lookup_33_of_meets_constraints h)
          (lookup_34_of_meets_constraints h)
          (lookup_35_of_meets_constraints h)
          (lookup_36_of_meets_constraints h)
          (lookup_37_of_meets_constraints h)
          (lookup_38_of_meets_constraints h)
          (lookup_39_of_meets_constraints h)
          (lookup_40_of_meets_constraints h)
          (lookup_41_of_meets_constraints h)
          (lookup_42_of_meets_constraints h)
          (lookup_43_of_meets_constraints h)
          (lookup_44_of_meets_constraints h)
          (lookup_45_of_meets_constraints h)
          (lookup_46_of_meets_constraints h)
          (fixed_of_meets_constraints h)
        have h_cols := rho_pi_chi_cells_col_0_1_in_normalize_4_cols i j
        have h_goal : ∀ idx: Fin rho_by_pi_num_word_parts, ∀ row < c.usable_rows,
          ∃ lookup_row, Lookups.Normalize_4.transform_table _ lookup_row = (
            c.get_advice (rho_pi_chi_column 0 j (2 * i + 3 * j) idx) row,
            c.get_advice (rho_pi_chi_column 1 j (2 * i + 3 * j) idx) row
          )
        := by
          intro idx row h_row
          specialize h_lookups
            (rho_pi_chi_column 0 j (2*i + 3*j) idx, rho_pi_chi_column 1 j (2*i + 3*j) idx)
            (h_cols idx)
            row
            h_row
          unfold Lookups.Normalize_4.transform_table Lookups.Normalize_4.input_by_row Lookups.Normalize_4.output_by_row
          obtain ⟨x0, x1, x2, x3, h_x0, h_x1, h_x2, h_x4, h_in, h_out⟩ := h_lookups
          simp_all
          use x0*64 + x1*16 + x2*4 + x3
          rewrite [if_pos (by omega)]
          congr <;> omega
        clear h_lookups h_cols
        have h_usable_rows := usable_rows_range_of_meets_constraints h
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
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩
        all_goals (
          subst h_cell_in
          simp [rho_pi_chi_location]
          apply h_goal; simp [rho_pi_chi_row, keccak_constants]
          apply lt_of_le_of_lt (Nat.mod_le _ c.n)
          omega
        )

  lemma os_parts_shuffle_true :
    os_parts_shuffle c
  := by
    unfold os_parts_shuffle
    intro round j i
    fin_cases j <;> fin_cases i <;> dsimp [os_parts]

end Keccak.Proofs

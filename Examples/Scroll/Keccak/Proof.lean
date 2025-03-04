import Examples.Scroll.Keccak.Gates.All
import Examples.Scroll.Keccak.Lookups.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  -- get_num_bits_per_lookup is implemented by loop in the rust, so a proof that my rewrite is equivalent
  lemma get_num_bits_per_lookup_correct (range: ℕ) (h_range: range ≥ 2):
    range^(get_num_bits_per_lookup range + 1) + keccak_unusable_rows > 2^get_degree ∧
    range^(get_num_bits_per_lookup range) + keccak_unusable_rows ≤ 2^get_degree := by
      simp_rw [get_num_bits_per_lookup, keccak_constants]
      norm_num
      apply And.intro
      . have h: 965 < range ^ (Nat.log range 965 + 1) := Nat.lt_pow_succ_log_self h_range 965
        omega
      . simp only [add_tsub_cancel_right, Nat.reduceLeDiff]
        simp [Nat.pow_log_le_self]

  lemma absorb_fat_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24,
      (absorb_fat c round).2
    := by
      intro round h_round
      replace h_round := Finset.mem_Icc.mp h_round
      have h_gate_0 := gate_0_of_meets_constraints h
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      unfold absorb_fat Split.expr
      convert Gates.Split.gate_0_split c h_fixed h_gate_0 (by omega) (round-1) (by omega) <;> omega

  lemma absorb_res_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24,
      (absorb_res c round).2
    := by
      intro round h_round
      unfold absorb_res Transform.split_expr
      simp [absorb_fat]
      split_ands
      . congr
        have := absorb_fat_of_meets_constraints h round h_round
        unfold absorb_fat Split.expr at this
        simp_all
      . rfl
      . simp [keccak_constants, Split.expr, Split.expr_res, word_parts_known, List.enum]
        intro num_bits_in cell_in num_bits_out cell_out h_mem
        have h_lookup_0 :=lookup_0_of_meets_constraints h
        have h_fixed := fixed_of_meets_constraints h
        have h_usable_rows := usable_rows_range_of_meets_constraints h
        have h_n := n_range_of_meets_constraints h
        have h_lookup_0 := Lookups.Normalize_3.lookup_0_normalize_3 c h_lookup_0 h_fixed
        replace h_round := (Finset.mem_Icc.mp h_round).2
        have : ∀ offset < 11, ∃ lookup_row,
          Lookups.Normalize_3.transform_table _ lookup_row =
          (c.get_advice 10 (12 * round + offset), c.get_advice 11 (12 * round + offset))
          := by
            intro offset hoffset
            specialize h_lookup_0 (12 * round + offset) (by omega)
            obtain ⟨x0, x1, x2, x3, x4, x5, h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_input, h_output⟩ := h_lookup_0
            rewrite [h_input, h_output]
            use x5 + 3*x4 + 9*x3 + 27*x2 + 81*x1 + 243*x0
            unfold Lookups.Normalize_3.transform_table
            rw [if_pos (by omega), Lookups.Normalize_3.input_by_row, Lookups.Normalize_3.output_by_row]
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
        all_goals (
          subst h_cell_in h_cell_out
          simp [cell_manager_to_raw]
          rewrite [Nat.mod_eq_of_lt (by omega)]
        )
        . exact this 0 (by trivial)
        all_goals refine this ?_ ?_ ; trivial

  lemma require_equal_absorb_result_of_meets_constraints (h: meets_constraints c):
    ∀ round ∈ Finset.Icc 1 24,
      require_equal_absorb_result c round
    := by
      intro round h_round
      replace h_round := Finset.mem_Icc.mp h_round
      have h_gate_1 := gate_1_of_meets_constraints h
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      unfold require_equal_absorb_result
      convert Gates.AbsorbResult.gate_1_absorb_result c h_fixed h_gate_1 (by omega) (round-1) (by omega)
      . unfold Split.constraint absorb_res Transform.split_expr
        simp
        funext
        congr
        omega
      . omega

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

  lemma os_parts_shuffle_of_meets_constraints :
    os_parts_shuffle c
  := by
    unfold os_parts_shuffle
    intro round j i
    fin_cases j <;> fin_cases i <;> dsimp [os_parts]

end Keccak.Proofs

import Examples.Scroll.Keccak.Gates.AbsorbResult
import Examples.Scroll.Keccak.Gates.AbsorbResultCopy.All
import Examples.Scroll.Keccak.Gates.AbsorbStateCopy.All
import Examples.Scroll.Keccak.Gates.AbsorbVerifyInput.All
import Examples.Scroll.Keccak.Gates.Split
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.FirstRow
import Examples.Scroll.Keccak.ProgramProofs.InputChecks
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

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

  lemma absorb_positions_correct (i j: Fin 5):
    (i,j) ∈ absorb_positions ↔ (i: ℕ) + (j: ℕ)*5 < 17
  := by
    unfold absorb_positions
    obtain ⟨i, h_i⟩ := i
    obtain ⟨j, h_j⟩ := j
    dsimp only [Fin.val]
    match i with | 0 | 1 | 2 | 3 | 4 => match j with | 0 | 1 | 2 | 3 | 4 => simp

  lemma a_slice_correct (i j: Fin 5):
    (i, j) ∈ absorb_positions → absorb_positions.get? (a_slice i j) = .some (i, j)
  := by
    unfold absorb_positions a_slice
    obtain ⟨i, h_i⟩ := i
    obtain ⟨j, h_j⟩ := j
    dsimp only [Fin.val]
    match i with | 0 | 1 | 2 | 3 | 4 => match j with | 0 | 1 | 2 | 3 | 4 => simp

  lemma absorb_gate_of_meets_constraints (h: meets_constraints c) (i j: Fin 5):
    ∀ round, round = 0 ∨ round = 25 → absorb_gate c round i j
  := by
    intro round h_round
    simp [absorb_gate]
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    have h_boolean_is_final := boolean_is_final_of_meets_constraints h
    have h_is_final_disabled_on_first_row := is_final_disabled_on_first_row_of_meets_constraints h
    unfold absorb_positions
    fin_cases j <;> fin_cases i
    all_goals simp [a_slice, keccak_constants]
    . have h_gate_78 := Gates.AbsorbVerifyInput.gate_78_absorb_verify_input c h_fixed (gate_78_of_meets_constraints h) (by omega) round h_round
      have h_gate_79 := Gates.AbsorbResultCopy.gate_79_absorb_result_copy c h_fixed (gate_79_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_80 := Gates.AbsorbVerifyInput.gate_80_absorb_verify_input c h_fixed (gate_80_of_meets_constraints h) (by omega) round h_round
      have h_gate_81 := Gates.AbsorbResultCopy.gate_81_absorb_result_copy c h_fixed (gate_81_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_82 := Gates.AbsorbVerifyInput.gate_82_absorb_verify_input c h_fixed (gate_82_of_meets_constraints h) (by omega) round h_round
      have h_gate_83 := Gates.AbsorbResultCopy.gate_83_absorb_result_copy c h_fixed (gate_83_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_84 := Gates.AbsorbVerifyInput.gate_84_absorb_verify_input c h_fixed (gate_84_of_meets_constraints h) round h_round
      have h_gate_85 := Gates.AbsorbResultCopy.gate_85_absorb_result_copy c h_fixed (gate_85_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_86 := Gates.AbsorbVerifyInput.gate_86_absorb_verify_input c h_fixed (gate_86_of_meets_constraints h) round h_round
      have h_gate_87 := Gates.AbsorbResultCopy.gate_87_absorb_result_copy c h_fixed (gate_87_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_88 := Gates.AbsorbVerifyInput.gate_88_absorb_verify_input c h_fixed (gate_88_of_meets_constraints h) (by omega) round h_round
      have h_gate_89 := Gates.AbsorbResultCopy.gate_89_absorb_result_copy c h_fixed (gate_89_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_90 := Gates.AbsorbVerifyInput.gate_90_absorb_verify_input c h_fixed (gate_90_of_meets_constraints h) (by omega) round h_round
      have h_gate_91 := Gates.AbsorbResultCopy.gate_91_absorb_result_copy c h_fixed (gate_91_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_92 := Gates.AbsorbVerifyInput.gate_92_absorb_verify_input c h_fixed (gate_92_of_meets_constraints h) round h_round
      have h_gate_93 := Gates.AbsorbResultCopy.gate_93_absorb_result_copy c h_fixed (gate_93_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_94 := Gates.AbsorbVerifyInput.gate_94_absorb_verify_input c h_fixed (gate_94_of_meets_constraints h) round h_round
      have h_gate_95 := Gates.AbsorbResultCopy.gate_95_absorb_result_copy c h_fixed (gate_95_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_96 := Gates.AbsorbVerifyInput.gate_96_absorb_verify_input c h_fixed (gate_96_of_meets_constraints h) round h_round
      have h_gate_97 := Gates.AbsorbResultCopy.gate_97_absorb_result_copy c h_fixed (gate_97_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_98 := Gates.AbsorbVerifyInput.gate_98_absorb_verify_input c h_fixed (gate_98_of_meets_constraints h) (by omega) round h_round
      have h_gate_99 := Gates.AbsorbResultCopy.gate_99_absorb_result_copy c h_fixed (gate_99_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_100 := Gates.AbsorbVerifyInput.gate_100_absorb_verify_input c h_fixed (gate_100_of_meets_constraints h) (by omega) round h_round
      have h_gate_101 := Gates.AbsorbResultCopy.gate_101_absorb_result_copy c h_fixed (gate_101_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_102 := Gates.AbsorbVerifyInput.gate_102_absorb_verify_input c h_fixed (gate_102_of_meets_constraints h) (by omega) round h_round
      have h_gate_103 := Gates.AbsorbResultCopy.gate_103_absorb_result_copy c h_fixed (gate_103_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_104 := Gates.AbsorbVerifyInput.gate_104_absorb_verify_input c h_fixed (gate_104_of_meets_constraints h) round h_round
      have h_gate_105 := Gates.AbsorbResultCopy.gate_105_absorb_result_copy c h_fixed (gate_105_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_106 := Gates.AbsorbVerifyInput.gate_106_absorb_verify_input c h_fixed (gate_106_of_meets_constraints h) round h_round
      have h_gate_107 := Gates.AbsorbResultCopy.gate_107_absorb_result_copy c h_fixed (gate_107_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_108 := Gates.AbsorbVerifyInput.gate_108_absorb_verify_input c h_fixed (gate_108_of_meets_constraints h) round h_round
      have h_gate_109 := Gates.AbsorbResultCopy.gate_109_absorb_result_copy c h_fixed (gate_109_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_110 := Gates.AbsorbVerifyInput.gate_110_absorb_verify_input c h_fixed (gate_110_of_meets_constraints h) round h_round
      have h_gate_111 := Gates.AbsorbResultCopy.gate_111_absorb_result_copy c h_fixed (gate_111_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      by_cases continue_hash c (12*round) <;> simp_all
    . have h_gate_112 := Gates.AbsorbStateCopy.gate_112_absorb_state_copy c h_fixed (gate_112_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_112 <;> simp_all
    . have h_gate_113 := Gates.AbsorbStateCopy.gate_113_absorb_state_copy c h_fixed (gate_113_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_113 <;> simp_all
    . have h_gate_114 := Gates.AbsorbStateCopy.gate_114_absorb_state_copy c h_fixed (gate_114_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_114 <;> simp_all
    . have h_gate_115 := Gates.AbsorbStateCopy.gate_115_absorb_state_copy c h_fixed (gate_115_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_115 <;> simp_all
    . have h_gate_116 := Gates.AbsorbStateCopy.gate_116_absorb_state_copy c h_fixed (gate_116_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_116 <;> simp_all
    . have h_gate_117 := Gates.AbsorbStateCopy.gate_117_absorb_state_copy c h_fixed (gate_117_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_117 <;> simp_all
    . have h_gate_118 := Gates.AbsorbStateCopy.gate_118_absorb_state_copy c h_fixed (gate_118_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_118 <;> simp_all
    . have h_gate_119 := Gates.AbsorbStateCopy.gate_119_absorb_state_copy c h_fixed (gate_119_of_meets_constraints h) h_boolean_is_final h_is_final_disabled_on_first_row (by omega) round h_round
      cases h_gate_119 <;> simp_all

end Keccak.Proofs

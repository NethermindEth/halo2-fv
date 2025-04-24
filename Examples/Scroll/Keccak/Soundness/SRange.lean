import Examples.Scroll.Keccak.Soundness.Chi.All
import Examples.Scroll.Keccak.Soundness.Iota
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.ProgramProofs.Absorb
import Examples.Scroll.Keccak.ProgramProofs.Iota
import Examples.Scroll.Keccak.ProgramProofs.ProcessInputs

namespace Keccak.Soundness

  lemma s_range {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 114781288875642162538711578024368757323014499555913773950098 < P):
    (s c round i j).val ≤ Normalize.mask
  := by
    have h_mask: Normalize.mask < P := by unfold Normalize.mask; omega
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    by_cases h: round = 1
    . have h_absorb := Proofs.absorb_gate_of_meets_constraints h_meets_constraints i j 0 (by trivial)
      simp [absorb_gate.eq_def] at h_absorb
      have h_continue_hash: ¬continue_hash c 0 := by
        have h_fixed := fixed_of_meets_constraints h_meets_constraints
        simp [continue_hash.eq_def, start_new_hash.eq_def, ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1]
      simp_all
      by_cases h_positions: (i,j) ∈ absorb_positions
      . simp_all
        rewrite [←h_absorb]
        have h_a_slice: a_slice i j + 1 ∈ Finset.Icc 1 24 := by unfold absorb_positions at h_positions; fin_cases h_positions <;> decide
        have h_input := Proofs.input_bytes_of_meets_constraints h_meets_constraints (a_slice i j + 1) h_a_slice
        simp [
          input_bytes.eq_def, keccak_constants, Transform.split_expr.eq_def,
          Split.expr.eq_def, Split.constraint.eq_def, Split.expr_res.eq_def,
          word_parts_known
        ] at h_input
        have ⟨⟨h_packed_parts, h_absorb_data⟩, h_normalize⟩ := h_input
        rewrite [h_packed_parts] at h_normalize
        simp at h_normalize
        have h_cell_1:= h_normalize 8 (cell_manager c (a_slice i j + 1) 60) 8 (cell_manager c (a_slice i j + 1) 72)
        have h_cell_2:= h_normalize 8 (cell_manager c (a_slice i j + 1) 61) 8 (cell_manager c (a_slice i j + 1) 73)
        have h_cell_3:= h_normalize 8 (cell_manager c (a_slice i j + 1) 62) 8 (cell_manager c (a_slice i j + 1) 74)
        have h_cell_4:= h_normalize 8 (cell_manager c (a_slice i j + 1) 63) 8 (cell_manager c (a_slice i j + 1) 75)
        have h_cell_5:= h_normalize 8 (cell_manager c (a_slice i j + 1) 64) 8 (cell_manager c (a_slice i j + 1) 76)
        have h_cell_6:= h_normalize 8 (cell_manager c (a_slice i j + 1) 65) 8 (cell_manager c (a_slice i j + 1) 77)
        have h_cell_7:= h_normalize 8 (cell_manager c (a_slice i j + 1) 66) 8 (cell_manager c (a_slice i j + 1) 78)
        have h_cell_8:= h_normalize 8 (cell_manager c (a_slice i j + 1) 67) 8 (cell_manager c (a_slice i j + 1) 79)
        clear h_normalize
        simp_all
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_1
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_2
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_3
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_4
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_5
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_6
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_7
        apply Lookups.PackTable.apply_transform_table_input_range at h_cell_8
        rewrite [←h_absorb_data]
        simp [
          Decode.expr.eq_def,
          keccak_constants, ZMod.val_add, ZMod.val_mul
        ]
        apply le_trans (Nat.mod_le _ _)
        unfold Normalize.mask
        have : Fact (1 < P) := by constructor; omega
        have h_pow_24: ((2: ZMod P)^24).val ≤ 2^24 := by
          convert ZMod.val_pow_le
          . simp [ZMod.val_two_eq_two_mod]
            rw [Nat.mod_eq_of_lt (by omega)]
          . assumption
        exact
          add_le_add
            (Nat.mul_le_mul h_pow_24
              (add_le_add
                (Nat.mul_le_mul h_pow_24
                  (add_le_add
                    (Nat.mul_le_mul h_pow_24
                      (add_le_add
                        (Nat.mul_le_mul h_pow_24
                          (add_le_add
                            (Nat.mul_le_mul h_pow_24
                              (add_le_add
                                (Nat.mul_le_mul h_pow_24
                                  (add_le_add
                                    (Nat.mul_le_mul h_pow_24 h_cell_8)
                                    h_cell_7))
                                h_cell_6))
                            h_cell_5))
                        h_cell_4))
                    h_cell_3))
                h_cell_2))
            h_cell_1
      . simp_all
    . have ⟨_, _⟩:= Finset.mem_Icc.mp h_round
      have h_range_sub_one : 1 ≤ round - 1 ∧ round - 1 ≤ 24 := by omega
      have h_range_sub_one := Finset.mem_Icc.mpr h_range_sub_one
      have h_next_row := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨(round-1), h_range_sub_one⟩ i j
      simp [next_row_check.eq_def] at h_next_row
      rewrite [show round-1+1 = round by omega] at h_next_row
      rewrite [←h_next_row]
      rewrite [iota_s_roundConstant h_meets_constraints (by omega) h_range_sub_one]
      fin_cases i <;> fin_cases j <;> simp
      . rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask h_mask)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_0_1 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_0_2 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_0_3 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_0_4 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_1_0 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_1_1 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_1_2 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_1_3 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_1_4 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_2_0 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_2_1 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_2_2 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_2_3 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_2_4 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_3_0 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_3_1 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_3_2 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_3_3 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_3_4 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_4_0 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_4_1 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_4_2 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_4_3 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask
      . rewrite [chi_os'_4_4 h_meets_constraints h_range_sub_one (by omega)]
        exact Normalize.normalize_unpacked_64_le_mask



end Keccak.Soundness

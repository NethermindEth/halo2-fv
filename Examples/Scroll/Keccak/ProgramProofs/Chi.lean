import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma chi_base_of_meets_constraints (idx: Finset.Icc 0 num_rho_pi_chi_columns) (i: Fin 5) (h: meets_constraints c):
    chi_base c idx i
  := by
    unfold chi_base chi_base_input'
    simp [keccak_constants, Scatter.expr, chi_base_input]
    obtain ⟨i, h_i⟩ := i
    obtain ⟨idx, h_idx⟩ := idx
    simp [Fin.add_def, Fin.coe_ofNat_eq_mod]
    intro row h_row
    simp [Lookups.PackTable.pack, Lookups.PackTable.pack_with_base, keccak_constants]
    norm_num
    simp [chi_base_output, cell_manager_column, keccak_constants]
    replace h_idx := Finset.mem_Icc.mp h_idx
    simp_all [keccak_constants]
    unfold Lookups.ChiBase.transform_table
    have h_fixed := fixed_of_meets_constraints h
    have h_goal (col0 col1 col2 col3: ℕ) (h_lookup: ∃ x0 x1 x2 x3,
      x0 < 5 ∧ x1 < 5 ∧ x2 < 5 ∧ x3 < 5 ∧
      1755 - 2 * c.get_advice col0 row + c.get_advice col1 row - c.get_advice col2 row = Lookups.ChiBase.input _ x0 x1 x2 x3 ∧
      c.get_advice col3 row = Lookups.ChiBase.output _ x0 x1 x2 x3
    ) (h_col0: col0 = 70 + idx * 5 + i) (h_col1: col1 = 70 + idx * 5 + (i + 1) % 5) (h_col2: col2 = (70 + idx * 5 + (i + 2) % 5)) (h_col3: col3 = (105 + idx * 5 + i)):
      ∃ lookup_row,
        (1755 - 2 * c.get_advice (70 + idx * 5 + i) row + c.get_advice (70 + idx * 5 + (i + 1) % 5) row -
              c.get_advice (70 + idx * 5 + (i + 2) % 5) row,
            c.get_advice (105 + idx * 5 + i) row) =
          Lookups.ChiBase.transform_table _ lookup_row
    := by
      obtain ⟨x0, x1, x2, x3, h_x0, h_x1, h_x2, h_x3, h_in, h_out⟩ := h_lookup
      unfold Lookups.ChiBase.transform_table
      simp_all
      simp_all [Lookups.ChiBase.input_by_row, Lookups.ChiBase.output_by_row]
      use x0*125 + x1*25 + x2*5 + x3
      rw [if_pos (by omega)]
      congr <;> omega
    match idx with
      | 0 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_50_chi_base c (lookup_50_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_51_chi_base c (lookup_51_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_52_chi_base c (lookup_52_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_53_chi_base c (lookup_53_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_54_chi_base c (lookup_54_of_meets_constraints h) h_fixed row h_row) <;> rfl
      | 1 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_55_chi_base c (lookup_55_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_56_chi_base c (lookup_56_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_57_chi_base c (lookup_57_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_58_chi_base c (lookup_58_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_59_chi_base c (lookup_59_of_meets_constraints h) h_fixed row h_row) <;> rfl
      | 2 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_60_chi_base c (lookup_60_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_61_chi_base c (lookup_61_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_62_chi_base c (lookup_62_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_63_chi_base c (lookup_63_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_64_chi_base c (lookup_64_of_meets_constraints h) h_fixed row h_row) <;> rfl
      | 3 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_65_chi_base c (lookup_65_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_66_chi_base c (lookup_66_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_67_chi_base c (lookup_67_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_68_chi_base c (lookup_68_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_69_chi_base c (lookup_69_of_meets_constraints h) h_fixed row h_row) <;> rfl
      | 4 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_70_chi_base c (lookup_70_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_71_chi_base c (lookup_71_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_72_chi_base c (lookup_72_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_73_chi_base c (lookup_73_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_74_chi_base c (lookup_74_of_meets_constraints h) h_fixed row h_row) <;> rfl
      | 5 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_75_chi_base c (lookup_75_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_76_chi_base c (lookup_76_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_77_chi_base c (lookup_77_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_78_chi_base c (lookup_78_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_79_chi_base c (lookup_79_of_meets_constraints h) h_fixed row h_row) <;> rfl
      | 6 => match i with
        | 0 => (apply h_goal; exact Lookups.ChiBase.lookup_80_chi_base c (lookup_80_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 1 => (apply h_goal; exact Lookups.ChiBase.lookup_81_chi_base c (lookup_81_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 2 => (apply h_goal; exact Lookups.ChiBase.lookup_82_chi_base c (lookup_82_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 3 => (apply h_goal; exact Lookups.ChiBase.lookup_83_chi_base c (lookup_83_of_meets_constraints h) h_fixed row h_row) <;> rfl
        | 4 => (apply h_goal; exact Lookups.ChiBase.lookup_84_chi_base c (lookup_84_of_meets_constraints h) h_fixed row h_row) <;> rfl



end Keccak.Proofs

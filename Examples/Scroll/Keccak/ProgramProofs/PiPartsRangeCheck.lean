import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma pi_parts_range_check_of_meets_constraints (h: meets_constraints c):
    ∀ idx: Finset.Ico pi_region_start pi_region_end, ∀ row < c.usable_rows,
      pi_parts_range_check c idx row
  := by
    intro idx row h_row
    obtain ⟨idx, h_idx⟩ := idx
    unfold pi_region_start pi_region_end at h_idx
    unfold pi_parts_range_check cell_manager_column
    simp [h_row]
    have h_fixed := fixed_of_meets_constraints h
    have h_lookup_47 := Lookups.Normalize_4.lookup_47_normalize_4 c (lookup_47_of_meets_constraints h) h_fixed row h_row
    have h_lookup_48 := Lookups.Normalize_4.lookup_48_normalize_4 c (lookup_48_of_meets_constraints h) h_fixed row h_row
    have h_lookup_49 := Lookups.Normalize_4.lookup_49_normalize_4 c (lookup_49_of_meets_constraints h) h_fixed row h_row
    dsimp [Lookups.Normalize_4.transform_table]
    obtain ⟨x140_0, x140_1, x140_2, x140_3, h_x140_0, h_x140_1, h_x140_2, h_x140_3, h_140⟩ := h_lookup_47
    obtain ⟨x141_0, x141_1, x141_2, x141_3, h_x141_0, h_x141_1, h_x141_2, h_x141_3, h_141⟩ := h_lookup_48
    obtain ⟨x142_0, x142_1, x142_2, x142_3, h_x142_0, h_x142_1, h_x142_2, h_x142_3, h_142⟩ := h_lookup_49
    simp [Lookups.Normalize_4.input_by_row]
    by_cases h_col: 7+↑idx/12 = 140
    . use x140_0*64 + x140_1*16 + x140_2*4 + x140_3
      rewrite [if_pos (by omega)]
      convert h_140 <;> omega
    by_cases h_col': 7+↑idx/12 = 141
    . use x141_0*64 + x141_1*16 + x141_2*4 + x141_3
      rewrite [if_pos (by omega)]
      convert h_141 <;> omega
    by_cases h_col'': 7+↑idx/12 = 142
    . use x142_0*64 + x142_1*16 + x142_2*4 + x142_3
      rewrite [if_pos (by omega)]
      convert h_142 <;> omega
    . have h_idx := Finset.mem_Icc.mp h_idx
      omega

end Keccak.Proofs

import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  @[normalize_rho] lemma normalize_rho_0_2_0 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 844 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 424).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_1 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 845 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 425).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_2 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 846 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 426).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_3 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 847 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 427).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_4 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 848 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 428).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_5 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 849 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 429).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_6 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 850 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 430).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_7 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 851 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 431).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_8 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 900 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 480).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_9 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 901 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 481).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_10 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 902 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 482).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_11 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 903 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 483).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_12 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 904 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 484).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_13 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 905 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 485).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_14 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 906 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 486).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_0_2_15 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 907 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 487).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

end Keccak.Soundness

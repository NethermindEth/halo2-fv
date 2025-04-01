import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  @[normalize_rho] lemma normalize_rho_1_1_0 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 768 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 348).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_1 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 769 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 349).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_2 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 770 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 350).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_3 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 771 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 351).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_4 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 772 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 352).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_5 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 773 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 353).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_6 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 774 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 354).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_7 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 775 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 355).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_8 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 776 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 356).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_9 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 777 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 357).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_10 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 778 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 358).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_11 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 779 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 359).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_12 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 828 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 408).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_13 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 829 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 409).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_14 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 830 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 410).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

  @[normalize_rho] lemma normalize_rho_1_1_15 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 831 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 411).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 1
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

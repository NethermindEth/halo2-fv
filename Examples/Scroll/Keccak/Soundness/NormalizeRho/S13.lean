import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  @[normalize_rho] lemma normalize_rho_1_3_0 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 856 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 436).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_1_3_1 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 857 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 437).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    simp [fin_vals] at h_row
    rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
      Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
    ]
    simp [row']
    by_cases row < 256 <;> simp_all [if_pos, if_neg]

  @[normalize_rho] lemma normalize_rho_1_3_2 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 858 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 438).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_3 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 859 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 439).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_4 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 860 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 440).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_5 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 861 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 441).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_6 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 862 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 442).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_7 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 863 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 443).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_8 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 912 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 492).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_9 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 913 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 493).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_10 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 914 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 494).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_11 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 915 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 495).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_12 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 916 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 496).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_13 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 917 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 497).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_14 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 918 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 498).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

  @[normalize_rho] lemma normalize_rho_1_3_15 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 919 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 499).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 3
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

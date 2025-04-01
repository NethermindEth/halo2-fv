import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  @[normalize_rho] lemma normalize_rho_1_0_0 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 884 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 464).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_1 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 885 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 465).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_2 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 886 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 466).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_3 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 887 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 467).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_4 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 936 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 516).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_5 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 937 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 517).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_6 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 938 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 518).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_7 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 939 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 519).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_8 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 940 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 520).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_9 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 941 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 521).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_10 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 942 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 522).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_11 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 943 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 523).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_12 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 944 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 524).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_13 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 945 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 525).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_14 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 946 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 526).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

  @[normalize_rho] lemma normalize_rho_1_0_15 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756):
    cell_manager c round 947 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 527).val 4)
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 1 0
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

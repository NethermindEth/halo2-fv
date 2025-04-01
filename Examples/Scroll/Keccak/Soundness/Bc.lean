import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Theta
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Attributes
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_6
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness

  @[normalize_bc] lemma normalize_bc_0 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 120) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_1 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 121) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 1)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_2 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 122) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 2)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_3 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 123) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 3)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_4 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 124) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 4)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_5 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 125) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 5)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_6 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 126) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 6)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_7 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 127) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 7)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_8 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 128) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 8)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_9 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 129) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 9)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_10 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 130) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 10)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_11 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 131) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 11)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_12 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 132) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 12)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_13 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 133) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 13)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_14 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 134) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 14)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_15 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 135) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 15)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_16 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 136) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 16)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_17 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 137) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 17)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_18 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 138) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 18)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_19 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 139) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 19)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_20 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 140) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 20)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

  @[normalize_bc] lemma normalize_bc_21 [NeZero P] {c: ValidCircuit P P_Prime} (idx: Fin 5) (h: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 366):
    cell_manager c round (96 + 22 * ↑idx + 141) =
    ↑(Normalize.normalize_unpacked (cell_manager c round (96 + 22 * ↑idx + 21)).val 3)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.bc_of_meets_constraints h round h_round idx
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; clear h_transform
    apply Lookups.Normalize_6.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 216 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_6.output_by_row P lookup_row'),
      Lookups.Normalize_6.output_eq_normalized_input, ←h_lookup_row.1
    ]
    . simp [lookup_row']
      by_cases lookup_row < 216
      . rewrite [if_pos (by assumption)]; assumption
      . rewrite [if_neg (by assumption)]; trivial
    . assumption

end Keccak.Soundness

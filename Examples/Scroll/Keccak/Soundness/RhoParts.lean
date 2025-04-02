import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize

import Lean

namespace Keccak.Soundness

namespace ThisIsSoMeta

def returnTypeOfParams (a₁ a₂ : ℕ) := s!"(cell_manager c round {a₁}).val ≤ {a₂}"

def proofOfParams (a₁ a₂ : ℕ) :=
  s!"by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round {a₁} {a₂}
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    try simp [fin_vals] at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)"

section

open Lean Parser
set_option hygiene false in
elab "#register" a₁:num a₂:num a₃:num a₄:num : command => do
  let returnType : String := returnTypeOfParams a₁.getNat a₂.getNat
  let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the proof."
  let tRtStx : TSyntax `term := ⟨rtStx⟩

  let proof := proofOfParams a₃.getNat a₄.getNat
  let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
  let tProofStx : TSyntax `term := ⟨proofStx⟩
  
  let uniqueName := mkIdent (Name.mkSimple s!"someUniqueName{a₁.getNat}{a₂.getNat}{a₃.getNat}{a₄.getNat}")
  logInfo m!"Registering: {uniqueName}"
  Lean.Elab.Command.elabCommand
    (←`(lemma $uniqueName [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P) : $tRtStx := $tProofStx))
    
end

-- #eval lemmaOfParams 1 2 3 4
end ThisIsSoMeta

  lemma cell_336_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 336).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_337_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 337).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_338_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 338).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_339_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 339).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_340_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 340).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_341_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 341).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_342_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 342).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_343_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 343).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_344_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 344).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_345_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 345).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_346_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 346).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_347_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 347).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_396_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 396).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_397_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 397).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_398_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 398).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

  lemma cell_399_normalize_4_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 399).val ≤ 1755
  := by
    have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round 0 0
    simp [
      keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
      s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
      s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
    ] at h_s_transform
    obtain ⟨row, h_row⟩ := h_s_transform.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; clear h_s_transform
    apply Lookups.Normalize_4.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_4.input_range h_P (by aesop)

end Keccak.Soundness

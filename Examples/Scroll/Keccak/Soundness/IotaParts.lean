import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Lookups.ChiBase.All
import Examples.Scroll.Keccak.Lookups.Normalize_3.All
import Examples.Scroll.Keccak.ProgramProofs.Chi
import Examples.Scroll.Keccak.ProgramProofs.Iota
import Examples.Scroll.Keccak.Soundness.Attributes
import Examples.Scroll.Keccak.Soundness.Lookups.ChiBase
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_3
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  @[normalize_iota] lemma normalize_iota_parts_0 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1644 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1632).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_0_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1632 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1632).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_1 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1645 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1633).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_1_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1633 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1633).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_2 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1646 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1634).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_2_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1634 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1634).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_3 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1647 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1635).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_3_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1635 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1635).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_4 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1648 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1636).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_4_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1636 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1636).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_5 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1649 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1637).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_5_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1637 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1637).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_6 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1650 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1638).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_6_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1638 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1638).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_7 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1651 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1639).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_7_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1639 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1639).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_8 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1652 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1640).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_8_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1640 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1640).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_9 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1653 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1641).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_9_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1641 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1641).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.1; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  @[normalize_iota] lemma normalize_iota_parts_10 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 74899):
    cell_manager c round 1654 =
    ↑(Normalize.normalize_unpacked (cell_manager c round 1642).val 6)
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]; set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
    rw [
      ofNat_zmod_val (Lookups.Normalize_3.output_by_row P lookup_row'),
      Lookups.Normalize_3.output_eq_normalized_input (h_P := h_P), ←h_lookup_row.1
    ]
    simp [lookup_row']
    by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]

  lemma iota_parts_10_to_bitvec [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P:64 < P):
    cell_manager c round 1642 = Nat.cast (BitVec.ofNat (6*BIT_COUNT) (cell_manager c round 1642).val).toNat
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_split
    simp [h_split, Split.expr_res.eq_def, keccak_constants, word_parts_known] at h_transform; clear h_split
    obtain ⟨lookup_row, h_lookup_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2; clear h_transform
    apply Lookups.Normalize_3.apply_transform_table at h_lookup_row
    simp [keccak_constants, h_lookup_row.1]
    rewrite [Nat.mod_eq_of_lt]
    . simp
    . set lookup_row' := (if lookup_row < 729 then lookup_row else 0)
      have : lookup_row' < 729 := by simp [lookup_row']; by_cases lookup_row < 729 <;> simp_all [if_pos, if_neg]
      apply lt_of_le_of_lt (Lookups.Normalize_3.input_range (P := P) (by omega) this)
      trivial

  lemma rho_pi_chi_2_range_0 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_row: row < c.usable_rows) (h_P: 8 < P):
    (c.get_advice 105 row).val ≤ 585
  := by
    have h_chi_base_0 := Proofs.chi_base_of_meets_constraints ⟨0, by simp[keccak_constants]⟩ 0 h_meets_constraints
    unfold chi_base chi_base_input' chi_base_output rho_pi_chi_column_starts rho_pi_chi_column at h_chi_base_0
    simp [keccak_constants] at h_chi_base_0
    have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
    have h_n := n_range_of_meets_constraints h_meets_constraints
    specialize h_chi_base_0 row h_row
    obtain ⟨lookup_row, h_lookup_row⟩ := h_chi_base_0
    symm at h_lookup_row
    apply Lookups.ChiBase.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]
    apply Lookups.ChiBase.output_range
    . assumption

  lemma rho_pi_chi_2_range_1 [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_row: row < c.usable_rows) (h_P: 8 < P):
    (c.get_advice 110 row).val ≤ 585
  := by
    have h_chi_base_1 := Proofs.chi_base_of_meets_constraints ⟨1, by simp[keccak_constants]⟩ 0 h_meets_constraints
    unfold chi_base chi_base_input' chi_base_output rho_pi_chi_column_starts rho_pi_chi_column at h_chi_base_1
    simp [keccak_constants] at h_chi_base_1
    have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
    have h_n := n_range_of_meets_constraints h_meets_constraints
    specialize h_chi_base_1 row h_row
    obtain ⟨lookup_row, h_lookup_row⟩ := h_chi_base_1
    symm at h_lookup_row
    apply Lookups.ChiBase.apply_transform_table at h_lookup_row
    rewrite [h_lookup_row.2]
    apply Lookups.ChiBase.output_range
    . assumption

  lemma os'_0_0_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (os' c round 0 0).val ≤ Normalize.mask
  := by
    simp [os'.eq_def, keccak_constants, list_ops, Decode.expr.eq_def, rho_pi_chi_cells.eq_def, cell_manager_to_raw]
    have h_chi_base_0 := Proofs.chi_base_of_meets_constraints ⟨0, by simp[keccak_constants]⟩ 0 h_meets_constraints
    have h_chi_base_1 := Proofs.chi_base_of_meets_constraints ⟨1, by simp[keccak_constants]⟩ 0 h_meets_constraints
    unfold chi_base chi_base_input' chi_base_output rho_pi_chi_column_starts rho_pi_chi_column at h_chi_base_0
    unfold chi_base chi_base_input' chi_base_output rho_pi_chi_column_starts rho_pi_chi_column at h_chi_base_1
    simp [keccak_constants] at h_chi_base_0 h_chi_base_1
    have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have h_x1 := rho_pi_chi_2_range_1 h_meets_constraints (show (12*round+3)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x1 := c.get_advice 110 ((12*round+3)%c.n)
    have h_x2 := rho_pi_chi_2_range_1 h_meets_constraints (show (12*round+2)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x2 := c.get_advice 110 ((12*round+2)%c.n)
    have h_x3 := rho_pi_chi_2_range_1 h_meets_constraints (show (12*round+1)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x3 := c.get_advice 110 ((12*round+1)%c.n)
    have h_x4 := rho_pi_chi_2_range_1 h_meets_constraints (show (12*round)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x4 := c.get_advice 110 ((12*round)%c.n)
    have h_x5 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+11)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x5 := c.get_advice 105 ((12*round+11)%c.n)
    have h_x6 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+10)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x6 := c.get_advice 105 ((12*round+10)%c.n)
    have h_x7 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+9)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x7 := c.get_advice 105 ((12*round+9)%c.n)
    have h_x8 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+8)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x8 := c.get_advice 105 ((12*round+8)%c.n)
    have h_x9 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+7)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x9 := c.get_advice 105 ((12*round+7)%c.n)
    have h_x10 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+6)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x10 := c.get_advice 105 ((12*round+6)%c.n)
    have h_x11 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+5)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x11 := c.get_advice 105 ((12*round+5)%c.n)
    have h_x12 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+4)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x12 := c.get_advice 105 ((12*round+4)%c.n)
    have h_x13 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+3)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x13 := c.get_advice 105 ((12*round+3)%c.n)
    have h_x14 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+2)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x14 := c.get_advice 105 ((12*round+2)%c.n)
    have h_x15 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round+1)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x15 := c.get_advice 105 ((12*round+1)%c.n)
    have h_x16 := rho_pi_chi_2_range_0 h_meets_constraints (show (12*round)%c.n < c.usable_rows by {
        have h_round := (Finset.mem_Icc.mp h_round).2
        apply lt_of_le_of_lt (Nat.mod_le _ _)
        omega
    }) (by omega)
    set x16 := c.get_advice 105 ((12*round)%c.n)
    simp [ZMod.val_add, ZMod.val_mul]
    have h_k: ((2: ZMod P)^12).val ≤ 2^12 := by
      convert ZMod.val_pow_le
      . rw [ZMod.val_two_eq_two_mod, Nat.mod_eq_of_lt (by omega)]
      . constructor; omega
    set k := (2: ZMod P)^12
    apply le_trans (Nat.mod_le _ _)
    have h_c_x1: k.val * x1.val ≤ 2^12*585 := Nat.mul_le_mul h_k h_x1
    simp at h_c_x1; set c_x1 := k.val * x1.val
    have h_c_x2: k.val * (c_x1 + x2.val) ≤ 2^12*(2396160+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x1 h_x2)
    simp at h_c_x2; set c_x2 := k.val * (c_x1 + x2.val)
    have h_c_x3: k.val * (c_x2 + x3.val) ≤ 2^12*(9817067520+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x2 h_x3)
    simp at h_c_x3; set c_x3 := k.val * (c_x2 + x3.val)
    have h_c_x4: k.val * (c_x3 + x4.val) ≤ 2^12*(40210710958080+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x3 h_x4)
    simp at h_c_x4; set c_x4 := k.val * (c_x3 + x4.val)
    have h_c_x5: k.val * (c_x4 + x5.val) ≤ 2^12*(164703072086691840+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x4 h_x5)
    simp at h_c_x5; set c_x5 := k.val * (c_x4 + x5.val)
    have h_c_x6: k.val * (c_x5 + x6.val) ≤ 2^12*(674623783267092172800+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x5 h_x6)
    simp at h_c_x6; set c_x6 := k.val * (c_x5 + x6.val)
    have h_c_x7: k.val * (c_x6 + x7.val) ≤ 2^12*(2763259016262009542184960+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x6 h_x7)
    simp at h_c_x7; set c_x7 := k.val * (c_x6 + x7.val)
    have h_c_x8: k.val * (c_x7 + x8.val) ≤ 2^12*(11318308930609191084791992320+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x7 h_x8)
    simp at h_c_x8; set c_x8 := k.val * (c_x7 + x8.val)
    have h_c_x9: k.val * (c_x8 + x9.val) ≤ 2^12*(46359793379775246683308002938880+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x8 h_x9)
    simp at h_c_x9; set c_x9 := k.val * (c_x8 + x9.val)
    have h_c_x10: k.val * (c_x9 + x10.val) ≤ 2^12*(189889713683559410414829580040048640+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x9 h_x10)
    simp at h_c_x10; set c_x10 := k.val * (c_x9 + x10.val)
    have h_c_x11: k.val * (c_x10 + x11.val) ≤ 2^12*(777788267247859345059141959844041625600+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x10 h_x11)
    simp at h_c_x11; set c_x11 := k.val * (c_x10 + x11.val)
    have h_c_x12: k.val * (c_x11 + x12.val) ≤ 2^12*(3185820742647231877362245467521194500853760+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x11 h_x12)
    simp at h_c_x12; set c_x12 := k.val * (c_x11 + x12.val)
    have h_c_x13: k.val * (c_x12 + x13.val) ≤ 2^12*(13049121761883061769675757434966812675499397120+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x12 h_x13)
    simp at h_c_x13; set c_x13 := k.val * (c_x12 + x13.val)
    have h_c_x14: k.val * (c_x13 + x14.val) ≤ 2^12*(53449202736673021008591902453624064718845532999680+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x13 h_x14)
    simp at h_c_x14; set c_x14 := k.val * (c_x13 + x14.val)
    have h_c_x15: k.val * (c_x14 + x15.val) ≤ 2^12*(218927934409412694051192432450044169088391303169085440+585) := Nat.mul_le_mul h_k (Nat.add_le_add h_c_x14 h_x15)
    simp at h_c_x15; set c_x15 := k.val * (c_x14 + x15.val)
    have h_c_x16: c_x15 + x16.val ≤ 896728819340954394833684203315380916586050777780576358400 + 585 := Nat.add_le_add h_c_x15 h_x16
    simp at h_c_x16
    exact h_c_x16

    lemma round_cst_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 9223372036854808576 < P):
      (round_cst c (get_num_rows_per_round * round)).val ≤ Normalize.mask
    := by
      have h_fixed := fixed_of_meets_constraints h_meets_constraints
      simp [keccak_constants, round_cst.eq_def, ValidCircuit.get_fixed, h_fixed, fixed_func, Normalize.mask.eq_def]
      have h_1: (1: ZMod P).val = 1 := by
        convert ZMod.val_natCast 1
        . simp
        . rw [Nat.mod_eq_of_lt]; omega
      have h_8: (8: ZMod P).val = 8 := by
        convert ZMod.val_natCast 8
        rw [Nat.mod_eq_of_lt]; omega
      have h_2097664: (2097664: ZMod P).val = 2097664 := by
        convert ZMod.val_natCast 2097664
        rw [Nat.mod_eq_of_lt]; omega
      have h_2097672: (2097672: ZMod P).val = 2097672 := by
        convert ZMod.val_natCast 2097672
        rw [Nat.mod_eq_of_lt]; omega
      have h_35184372089352: (35184372089352: ZMod P).val = 35184372089352 := by
        convert ZMod.val_natCast 35184372089352
        rw [Nat.mod_eq_of_lt]; omega
      have h_35184374185992: (35184374185992: ZMod P).val = 35184374185992 := by
        convert ZMod.val_natCast 35184374185992
        rw [Nat.mod_eq_of_lt]; omega
      have h_35184374186505: (35184374186505: ZMod P).val = 35184374186505 := by
        convert ZMod.val_natCast 35184374186505
        rw [Nat.mod_eq_of_lt]; omega
      have h_9223372036854775808 : (9223372036854775808: ZMod P).val = 9223372036854775808 := by
        convert ZMod.val_natCast 9223372036854775808
        rw [Nat.mod_eq_of_lt]; omega
      have h_9223372036854808576 : (9223372036854808576: ZMod P).val = 9223372036854808576 := by
        convert ZMod.val_natCast 9223372036854808576
        rw [Nat.mod_eq_of_lt]; omega
      match round with
        | 0 => simp at h_round
        | 1 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, *]
        | 2 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, *]
        | 3 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 4 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 5 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, *]
        | 6 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 7 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 8 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 9 => simp [fixed_func_col_7, fixed_func_col_7_0_to_119, *]
        | 10 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, *]
        | 11 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 12 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 13 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 14 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 15 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 16 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 17 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 18 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 19 => simp [fixed_func_col_7, fixed_func_col_7_120_to_239, *]
        | 20 => simp [fixed_func_col_7, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 21 => simp [fixed_func_col_7, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 22 => simp [fixed_func_col_7, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 23 => simp [fixed_func_col_7, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | 24 => simp [fixed_func_col_7, ZMod.val_mul, ZMod.val_add, mul_assoc, Nat.add_mul, add_assoc, *]; exact le_trans (Nat.mod_le _ P) (by trivial)
        | _+25 => simp at h_round

  lemma cell_1632_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1632).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1633_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1633).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1634_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1634).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1635_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1635).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1636_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1636).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1637_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1637).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1638_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1638).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1639_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1639).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1640_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1640).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.2.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1641_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1641).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.1
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1642_normalize_3_input_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (cell_manager c round 1642).val ≤ 74898
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    obtain ⟨row, h_row⟩ := h_transform.2.2.2.2.2.2.2.2.2.2
    apply Lookups.Normalize_3.apply_transform_table at h_row
    rewrite [h_row.1]
    exact Lookups.Normalize_3.input_range h_P (by aesop)

  lemma cell_1642_small_range [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 114781288875642162538711578024368757323014499555913773950098 < P):
    (cell_manager c round 1642).val ≤ 1170 -- 0b010010010010
  := by
    have ⟨h_split, _, h_transform⟩ := Proofs.iota_s_0_0_transform_of_meets_constraints h_meets_constraints ⟨round, h_round⟩
    simp [
      Split.expr.eq_def, Split.expr_res.eq_def, keccak_constants,
      word_parts_known, Split.constraint.eq_def, iota_input.eq_def,
      iota_parts.eq_def
    ] at h_split
    have h_le: (os' c round 0 0 + round_cst c (12*round)).val ≤ Normalize.mask + Normalize.mask := by
      have h_os := os'_0_0_range h_meets_constraints h_round (by omega)
      have h_round_cst := round_cst_range h_meets_constraints h_round (by omega)
      rewrite [ZMod.val_add, Nat.mod_eq_of_lt]
      . exact add_le_add h_os h_round_cst
      . apply lt_of_le_of_lt
        . exact add_le_add h_os h_round_cst
        . simp [Normalize.mask.eq_def]
          omega
    have (a b: ZMod P) (h: a = b): a.val = b.val := by simp_all
    apply this at h_split; clear this
    rewrite [←h_split] at h_le
    have : (262144: ZMod P).val = 262144 := by
      convert ZMod.val_natCast 262144
      rw [Nat.mod_eq_of_lt]; omega
    simp [
      Normalize.mask.eq_def, Decode.expr.eq_def, keccak_constants,
      zmod_pow_simps, ZMod.val_add, ZMod.val_mul,
      this, mul_add, ←mul_assoc
    ] at h_le
    simp [
      iota_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def,
      list_ops, keccak_constants, word_parts_known
    ] at h_transform
    set rest := 2^162 * (cell_manager c round 1641).val +
                    2^144 * (cell_manager c round 1640).val +
                  2^126 * (cell_manager c round 1639).val +
                2^108 * (cell_manager c round 1638).val +
              2^90 * (cell_manager c round 1637).val +
            2^72 * (cell_manager c round 1636).val +
          2^54 * (cell_manager c round 1635).val +
        2^36 * (cell_manager c round 1634).val +
      2^18 * (cell_manager c round 1633).val +
    (cell_manager c round 1632).val
    have h_rest: rest ≤ 2^162 * 74898 +
                    2^144 * 74898 +
                  2^126 * 74898 +
                2^108 * 74898 +
              2^90 * 74898 +
            2^72 * 74898 +
          2^54 * 74898 +
        2^36 * 74898 +
      2^18 * 74898 +
    74898
    := by
      apply Nat.add_le_add
      . apply Nat.add_le_add
        . apply Nat.add_le_add
          . apply Nat.add_le_add
            . apply Nat.add_le_add
              . apply Nat.add_le_add
                . apply Nat.add_le_add
                  . apply Nat.add_le_add
                    . apply Nat.add_le_add
                      . apply Nat.mul_le_mul_left
                        . exact cell_1641_normalize_3_input_range h_meets_constraints h_round (by omega)
                      . apply Nat.mul_le_mul_left
                        . exact cell_1640_normalize_3_input_range h_meets_constraints h_round (by omega)
                    . apply Nat.mul_le_mul_left
                      . exact cell_1639_normalize_3_input_range h_meets_constraints h_round (by omega)
                  . apply Nat.mul_le_mul_left
                    . exact cell_1638_normalize_3_input_range h_meets_constraints h_round (by omega)
                . apply Nat.mul_le_mul_left
                  . exact cell_1637_normalize_3_input_range h_meets_constraints h_round (by omega)
              . apply Nat.mul_le_mul_left
                . exact cell_1636_normalize_3_input_range h_meets_constraints h_round (by omega)
            . apply Nat.mul_le_mul_left
              . exact cell_1635_normalize_3_input_range h_meets_constraints h_round (by omega)
          . apply Nat.mul_le_mul_left
            . exact cell_1634_normalize_3_input_range h_meets_constraints h_round (by omega)
        . apply Nat.mul_le_mul_left
          . exact cell_1633_normalize_3_input_range h_meets_constraints h_round (by omega)
      . exact cell_1632_normalize_3_input_range h_meets_constraints h_round (by omega)
    have h_le :
      (2^180 * (cell_manager c round 1642).val + rest) % P ≤ Normalize.mask + Normalize.mask
    := by
      simp [rest, ←add_assoc, Normalize.mask.eq_def]
      exact h_le
    have h_le' :
      (2^180 * (cell_manager c round 1642).val + rest) ≤ 114781288875642162538711578024368757323014499555913773950098
    := by
      apply Nat.add_le_add (d := 437855868818825388102384864900088338176782606338172050)
      . convert Nat.mul_le_mul_left
          (2^180)
          (cell_1642_normalize_3_input_range h_meets_constraints h_round (by omega))
      . exact h_rest
    rewrite [Nat.mod_eq_of_lt] at h_le
    . simp [Normalize.mask.eq_def] at h_rest h_le
      by_cases (cell_manager c round 1642).val ≤ 1170
      . assumption
      . omega
    . omega

  lemma iota_parts_10_to_bitvec' [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 114781288875642162538711578024368757323014499555913773950098 < P):
    cell_manager c round 1642 = Nat.cast (BitVec.ofNat (4*BIT_COUNT) (cell_manager c round 1642).val).toNat
  := by
    have h := cell_1642_small_range h_meets_constraints h_round h_P
    simp_all [keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega)]
    aesop

end Keccak.Soundness

import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Theta
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_6
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.SRange

namespace Keccak.Soundness

  namespace BcRange
    def cell_offset (n: ℕ) :=
      match n with
        | 0 => ""
        | _ => s!" + {n}"

    def returnTypeOfParams (cell : ℕ) :=
      let offset := cell_offset cell
      s!"(cell_manager c round (96 + 22 * ↑idx{offset})).val ≤ 365"

    def transformIndex (n: ℕ) :=
      match n with
        | 0 => ".1"
        | 21 => ".2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2"
        | m+1 =>
          let r := transformIndex m
          s!".2{r}"

    def proofOfParams (n : ℕ) :=
      let idx := transformIndex n
      s!"by
        have ⟨_, h_s_transform⟩ := Proofs.bc_of_meets_constraints h_meets_constraints round h_round idx
        simp [
          keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
          c_parts.eq_def, Split.expr.eq_def, Split.expr_res.eq_def
        ] at h_s_transform
        obtain ⟨row, h_row⟩ := h_s_transform{idx}; clear h_s_transform
        apply Lookups.Normalize_6.apply_transform_table at h_row
        rewrite [h_row.1]
        exact Lookups.Normalize_6.input_range h_P (by aesop)"

    open Lean Parser
    set_option hygiene false in
    elab "#register_bc_normalize_6_input_range" n:num : command => do
      let returnType : String := returnTypeOfParams n.getNat
      let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the returnType."
      let tRtStx : TSyntax `term := ⟨rtStx⟩

      let proof := proofOfParams n.getNat
      let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
      let tProofStx : TSyntax `term := ⟨proofStx⟩

      let uniqueName := mkIdent (Name.mkSimple s!"bc_{n.getNat}_normalize_6_input_range")
      -- logInfo m!"Registering: {uniqueName}"
      Lean.Elab.Command.elabCommand
        (←`(lemma $uniqueName [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P) (idx: Fin 5): $tRtStx := $tProofStx))
  end BcRange

  #register_bc_normalize_6_input_range 0
  #register_bc_normalize_6_input_range 1
  #register_bc_normalize_6_input_range 2
  #register_bc_normalize_6_input_range 3
  #register_bc_normalize_6_input_range 4
  #register_bc_normalize_6_input_range 5
  #register_bc_normalize_6_input_range 6
  #register_bc_normalize_6_input_range 7
  #register_bc_normalize_6_input_range 8
  #register_bc_normalize_6_input_range 9
  #register_bc_normalize_6_input_range 10
  #register_bc_normalize_6_input_range 11
  #register_bc_normalize_6_input_range 12
  #register_bc_normalize_6_input_range 13
  #register_bc_normalize_6_input_range 14
  #register_bc_normalize_6_input_range 15
  #register_bc_normalize_6_input_range 16
  #register_bc_normalize_6_input_range 17
  #register_bc_normalize_6_input_range 18
  #register_bc_normalize_6_input_range 19
  #register_bc_normalize_6_input_range 20
  #register_bc_normalize_6_input_range 21

  -- This bound on P is slightly lax, the actual value is between 2^198 and 2^197
  lemma bc_top_part_range {c: ValidCircuit P P_Prime} (idx: Fin 5) (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P):
    (cell_manager c round (96 + 22*↑idx+21)).val ≤ 5
  := by
    norm_num at h_P
    have := Proofs.bc_of_meets_constraints h_meets_constraints round h_round idx
    simp [
      bc.eq_def, keccak_constants, Transform.split_expr.eq_def,
      Split.expr.eq_def, Split.constraint.eq_def,
    ] at this
    have ⟨⟨h_c_parts, h_decode⟩,h_lookup⟩ := this
    clear this
    simp [
      Decode.expr.eq_def, keccak_constants, Split.expr_res.eq_def,
      word_parts_known, mul_add, ←mul_assoc, ←pow_add
    ] at h_decode
    have (a b: ZMod P) (h: a = b): a.val = b.val := by simp_all
    apply this at h_decode
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    simp [ZMod.val_add, ZMod.val_mul] at h_decode
    simp [h_c_parts, Split.expr_res, word_parts_known, add_assoc] at h_lookup
    simp [←add_assoc] at h_lookup
    have h_cell_1 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx)) 3 (cell_manager c round (96 + 22*↑idx + 120))
    simp at h_cell_1
    have h_cell_2 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 1)) 3 (cell_manager c round (96 + 22*↑idx + 121))
    simp at h_cell_2
    have h_cell_3 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 2)) 3 (cell_manager c round (96 + 22*↑idx + 122))
    simp at h_cell_3
    have h_cell_4 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 3)) 3 (cell_manager c round (96 + 22*↑idx + 123))
    simp at h_cell_4
    have h_cell_5 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 4)) 3 (cell_manager c round (96 + 22*↑idx + 124))
    simp at h_cell_5
    have h_cell_6 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 5)) 3 (cell_manager c round (96 + 22*↑idx + 125))
    simp at h_cell_6
    have h_cell_7 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 6)) 3 (cell_manager c round (96 + 22*↑idx + 126))
    simp at h_cell_7
    have h_cell_8 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 7)) 3 (cell_manager c round (96 + 22*↑idx + 127))
    simp at h_cell_8
    have h_cell_9 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 8)) 3 (cell_manager c round (96 + 22*↑idx + 128))
    simp at h_cell_9
    have h_cell_10 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 9)) 3 (cell_manager c round (96 + 22*↑idx + 129))
    simp at h_cell_10
    have h_cell_11 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 10)) 3 (cell_manager c round (96 + 22*↑idx + 130))
    simp at h_cell_11
    have h_cell_12 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 11)) 3 (cell_manager c round (96 + 22*↑idx + 131))
    simp at h_cell_12
    have h_cell_13 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 12)) 3 (cell_manager c round (96 + 22*↑idx + 132))
    simp at h_cell_13
    have h_cell_14 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 13)) 3 (cell_manager c round (96 + 22*↑idx + 133))
    simp at h_cell_14
    have h_cell_15 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 14)) 3 (cell_manager c round (96 + 22*↑idx + 134))
    simp at h_cell_15
    have h_cell_16 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 15)) 3 (cell_manager c round (96 + 22*↑idx + 135))
    simp at h_cell_16
    have h_cell_17 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 16)) 3 (cell_manager c round (96 + 22*↑idx + 136))
    simp at h_cell_17
    have h_cell_18 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 17)) 3 (cell_manager c round (96 + 22*↑idx + 137))
    simp at h_cell_18
    have h_cell_19 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 18)) 3 (cell_manager c round (96 + 22*↑idx + 138))
    simp at h_cell_19
    have h_cell_20 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 19)) 3 (cell_manager c round (96 + 22*↑idx + 139))
    simp at h_cell_20
    have h_cell_21 := h_lookup 3 (cell_manager c round (96 + 22 * ↑idx + 20)) 3 (cell_manager c round (96 + 22*↑idx + 140))
    simp at h_cell_21
    have h_cell_22 := h_lookup 1 (cell_manager c round (96 + 22 * ↑idx + 21)) 1 (cell_manager c round (96 + 22*↑idx + 141))
    simp at h_cell_22
    clear h_lookup
    have (a b: ZMod P) (h: ∃ lookup_row, Lookups.Normalize_6.transform_table P lookup_row = (a, b))
    : a.val ≤ 365 := by
      obtain ⟨row, h⟩ := h
      apply Lookups.Normalize_6.apply_transform_table at h
      rewrite [h.1]
      convert Lookups.Normalize_6.input_range _ _
      . assumption
      . omega
      . by_cases h: row < 216 <;> simp [h]
    replace h_cell_1 := this _ _ h_cell_1
    replace h_cell_2 := this _ _ h_cell_2
    replace h_cell_3 := this _ _ h_cell_3
    replace h_cell_4 := this _ _ h_cell_4
    replace h_cell_5 := this _ _ h_cell_5
    replace h_cell_6 := this _ _ h_cell_6
    replace h_cell_7 := this _ _ h_cell_7
    replace h_cell_8 := this _ _ h_cell_8
    replace h_cell_9 := this _ _ h_cell_9
    replace h_cell_10 := this _ _ h_cell_10
    replace h_cell_11 := this _ _ h_cell_11
    replace h_cell_12 := this _ _ h_cell_12
    replace h_cell_13 := this _ _ h_cell_13
    replace h_cell_14 := this _ _ h_cell_14
    replace h_cell_15 := this _ _ h_cell_15
    replace h_cell_16 := this _ _ h_cell_16
    replace h_cell_17 := this _ _ h_cell_17
    replace h_cell_18 := this _ _ h_cell_18
    replace h_cell_19 := this _ _ h_cell_19
    replace h_cell_20 := this _ _ h_cell_20
    replace h_cell_21 := this _ _ h_cell_21
    replace h_cell_22 := this _ _ h_cell_22
    have : Fact (1 < P) := by constructor; omega
    have h_2: (2: ZMod P).val = 2 := by
      simp [ZMod.val_two_eq_two_mod]
      rw [Nat.mod_eq_of_lt (by omega)]
    rewrite [
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      ZMod.val_pow (by rewrite [h_2]; omega),
      h_2
    ] at h_decode
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_decode
    have h_s0:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 0)
    have h_s1:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 1)
    have h_s2:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 2)
    have h_s3:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 3)
    have h_s4:= s_range h_meets_constraints h_round (by omega) (i := idx) (j := 4)
    unfold Normalize.mask at h_s0 h_s1 h_s2 h_s3 h_s4
    rewrite [Nat.mod_eq_of_lt (by omega)] at h_decode
    by_cases h_range: (cell_manager c round (96 + 22 * ↑idx + 21)).val ≤ 5
    . assumption
    . exfalso; omega


  -- This bound on P is slightly lax, the actual value is between 2^198 and 2^197
  lemma bc_top_part_normalized_range {c: ValidCircuit P P_Prime} (idx: Fin 5) (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P):
    Normalize.normalize_unpacked (cell_manager c round (96 + 22*↑idx+21)).val 3 =
    Normalize.normalize_unpacked (cell_manager c round (96 + 22*↑idx+21)).val 1
  := by
    have := bc_top_part_range idx h_meets_constraints h_round h_P
    match h: (cell_manager c round (96 + 22 * ↑idx + 21)).val with
      | 0 | 1 | 2 | 3 | 4 | 5 => rewrite [h]; decide
      | _+6 => exfalso; omega
end Keccak.Soundness

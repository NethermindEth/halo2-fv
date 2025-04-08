import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.PiPartsRangeCheck
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.PiPartsRange
import Examples.Scroll.Keccak.Spec.FinVals

namespace Keccak.Soundness

  namespace RhoRange
    def returnTypeOfParams (cell : ℕ) := s!"(cell_manager c round {cell}).val ≤ 1755"

    def transformIndex (n: ℕ) :=
      match n with
        | 0 => ".1"
        | 15 => ".2.2.2.2.2.2.2.2.2.2.2.2.2.2.2"
        | m+1 =>
          let r := transformIndex m
          s!".2{r}"

    def proofOfParams (x y n : ℕ) :=
      let idx := transformIndex n
      s!"by
        have ⟨_, h_s_transform⟩ := Proofs.s_parts'_of_meets_constraints h_meets_constraints round h_round {x} {y}
        simp [
          keccak_constants, word_parts_known, target_part_sizes_known, get_rotate_count, list_ops,
          s_parts_cell_offsets, pi_region_start, SplitUniform.input_parts, rho_pi_chi_cells,
          s_parts.eq_def, SplitUniform.expr.eq_def, SplitUniform.expr_res.eq_def, SplitUniform.output_parts.eq_def
        ] at h_s_transform
        obtain ⟨row, h_row⟩ := h_s_transform{idx}; clear h_s_transform
        apply Lookups.Normalize_4.apply_transform_table at h_row
        try simp [fin_vals] at h_row
        rewrite [h_row.1]
        exact Lookups.Normalize_4.input_range h_P (by aesop)"

    open Lean Parser
    set_option hygiene false in
    elab "#register_rho_normalize_4_input_range" cell:num x:num y:num n:num : command => do
      let returnType : String := returnTypeOfParams cell.getNat
      let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the returnType."
      let tRtStx : TSyntax `term := ⟨rtStx⟩

      let proof := proofOfParams x.getNat y.getNat n.getNat
      let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
      let tProofStx : TSyntax `term := ⟨proofStx⟩

      let uniqueName := mkIdent (Name.mkSimple s!"cell_{cell.getNat}_normalize_4_input_range")
      -- logInfo m!"Registering: {uniqueName}"
      Lean.Elab.Command.elabCommand
        (←`(lemma $uniqueName [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P): $tRtStx := $tProofStx))
  end RhoRange

end Keccak.Soundness

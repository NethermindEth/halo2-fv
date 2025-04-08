import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness
  namespace NormalizeRho
    def returnTypeOfParams (cell: ℕ) :=
      s!"cell_manager c round {cell} =
      ↑(Normalize.normalize_unpacked (cell_manager c round {cell-420}).val 4)"

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
        rewrite [h_row.2]; set row' := (if row < 256 then row else 0)
        rw [
          ofNat_zmod_val (Lookups.Normalize_4.output_by_row P row'),
          Lookups.Normalize_4.output_eq_normalized_input (h_P := h_P), ←h_row.1
        ]
        simp [row']
        by_cases row < 256 <;> simp_all [if_pos, if_neg]"

    open Lean Parser
    set_option hygiene false in
    elab "#register_normalize_rho_transform" cell:num x:num y:num n:num : command => do
      let returnType : String := returnTypeOfParams cell.getNat
      let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the returnType."
      let tRtStx : TSyntax `term := ⟨rtStx⟩

      let proof := proofOfParams x.getNat y.getNat n.getNat
      let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
      let tProofStx : TSyntax `term := ⟨proofStx⟩

      let uniqueName := mkIdent (Name.mkSimple s!"normalize_rho_{x.getNat}_{y.getNat}_{n.getNat}")
      -- logInfo m!"Registering: {uniqueName}"
      Lean.Elab.Command.elabCommand
        (←`(@[normalize_rho] lemma $uniqueName [NeZero P] {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: P ≥ 1756): $tRtStx := $tProofStx))
  end NormalizeRho

end Keccak.Soundness

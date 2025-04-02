import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.PiPartsRangeCheck
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Spec.FinVals

namespace Keccak.Soundness
  namespace PiPartsRange

    def returnTypeOfParams (cell : ℕ) := s!"(cell_manager c round {cell}).val ≤ 1755"

    def proofOfParams (cell : ℕ) :=
      s!"by
        have : NeZero P := by constructor; exact P_Prime.ne_zero
        simp [cell_manager_to_col_row]
        have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
        have h_n := n_range_of_meets_constraints h_meets_constraints
        have := Proofs.pi_parts_range_check_of_meets_constraints h_meets_constraints ⟨
          {cell},
          by simp [pi_region_start, pi_region_end]
        ⟩ (cell_manager_row c round {cell})
        simp [
          pi_parts_range_check.eq_def, Lookups.Normalize_4.transform_table,
          cell_manager_column.eq_def, keccak_constants
        ] at this
        specialize this (by simp [cell_manager_row.eq_def]; rewrite [Nat.mod_eq_of_lt] <;> omega)
        obtain ⟨lookup_row, h_lookup_row⟩ := this
        simp [cell_manager_column.eq_def]
        rewrite [h_lookup_row]
        aesop (add simp Lookups.Normalize_4.input_range)"

    open Lean Parser
    set_option hygiene false in
    elab "#register_normalize_4_input_range" cell:num : command => do
      let returnType : String := returnTypeOfParams cell.getNat
      let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the returnType."
      let tRtStx : TSyntax `term := ⟨rtStx⟩

      let proof := proofOfParams cell.getNat
      let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
      let tProofStx : TSyntax `term := ⟨proofStx⟩

      let uniqueName := mkIdent (Name.mkSimple s!"cell_{cell.getNat}_normalize_4_input_range")
      logInfo m!"Registering: {uniqueName}"
      Lean.Elab.Command.elabCommand
        (←`(lemma $uniqueName {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round < 60) (h_P: 8 < P): $tRtStx := $tProofStx))

  end PiPartsRange

  #register_normalize_4_input_range 1596
  #register_normalize_4_input_range 1597
  #register_normalize_4_input_range 1598
  #register_normalize_4_input_range 1599
  #register_normalize_4_input_range 1600
  #register_normalize_4_input_range 1601
  #register_normalize_4_input_range 1602
  #register_normalize_4_input_range 1603
  #register_normalize_4_input_range 1604
  #register_normalize_4_input_range 1605
  #register_normalize_4_input_range 1606
  #register_normalize_4_input_range 1607
  #register_normalize_4_input_range 1608
  #register_normalize_4_input_range 1609
  #register_normalize_4_input_range 1610
  #register_normalize_4_input_range 1611
  #register_normalize_4_input_range 1612
  #register_normalize_4_input_range 1613
  #register_normalize_4_input_range 1614
  #register_normalize_4_input_range 1615
  #register_normalize_4_input_range 1616
  #register_normalize_4_input_range 1617
  #register_normalize_4_input_range 1618
  #register_normalize_4_input_range 1619
  #register_normalize_4_input_range 1620
  #register_normalize_4_input_range 1621
  #register_normalize_4_input_range 1622
  #register_normalize_4_input_range 1623
  #register_normalize_4_input_range 1624
  #register_normalize_4_input_range 1625
  #register_normalize_4_input_range 1626
  #register_normalize_4_input_range 1627
  #register_normalize_4_input_range 1628
  #register_normalize_4_input_range 1629
  #register_normalize_4_input_range 1630
  #register_normalize_4_input_range 1631


end Keccak.Soundness

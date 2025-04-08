import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Chi
import Examples.Scroll.Keccak.Soundness.BitInvert
import Examples.Scroll.Keccak.Soundness.Lookups.ChiBase
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  namespace ChiBase

  def returnTypeOfParams (out_cell in_cell1 in_cell2 in_cell3 : ℕ) := s!"c.get_advice {out_cell} row = Normalize.normalize_unpacked (
      (c.get_advice {in_cell1} row).val ^^^ (
        (bit_invert (c.get_advice {in_cell2} row).val 4) &&&
        (c.get_advice {in_cell3} row).val
      )
    ) 4"

    def proofOfParams (idx i in_cell1 in_cell2 in_cell3 : ℕ) :=
      s!"by
        simp [keccak_constants] at h_P
        have h_usable_rows := usable_rows_range_of_meets_constraints h_meets_constraints
        have h_chi_base := Proofs.chi_base_of_meets_constraints ⟨{idx}, by simp [keccak_constants]⟩ {i} h_meets_constraints row (by omega)
        obtain ⟨lookup_row, h_lookup_row⟩ := h_chi_base
        simp [
          chi_base, chi_base_input', keccak_constants,
          chi_base_input, chi_base_output
        ] at h_lookup_row
        symm at h_lookup_row
        apply Lookups.ChiBase.apply_transform_table at h_lookup_row
        set lookup_row' := (if lookup_row < 625 then lookup_row else 0)
        have : NeZero P := by constructor; exact P_Prime.ne_zero
        have h_1' := (Normalize.self_normalize_of_normalized_4 (c.get_advice {in_cell1} row) (by omega) h_1)
        have h_2' := (Normalize.self_normalize_of_normalized_4 (c.get_advice {in_cell2} row) (by omega) h_2)
        have h_3' := (Normalize.self_normalize_of_normalized_4 (c.get_advice {in_cell3} row) (by omega) h_3)
        have := Lookups.ChiBase.output_eq_transformed_input
          h_1' h_2' h_3'
          h_lookup_row.1
          (by simp [keccak_constants]; omega)
        rewrite [bit_invert_normalized_eq_xor h_2]
        rewrite [h_1', h_2', h_3']
        simp
        rewrite [
          Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
          Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
          Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
          Normalize.normalize_unpacked_xor,
          Normalize.normalize_unpacked_idempotent,
          Normalize.normalize_unpacked_and,
          Normalize.normalize_unpacked_idempotent,
          Normalize.normalize_unpacked_xor,
          Normalize.normalize_unpacked_idempotent,
          Normalize.normalize_unpacked_4095_4
        ]
        rewrite [h_1', h_2', h_3'] at this
        simp at this
        rewrite [
          Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
          Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
          Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by omega)),
          Normalize.and_normalize,
          Normalize.normalize_unpacked_xor,
          Normalize.normalize_unpacked_4095_4,
          Normalize.normalize_unpacked_idempotent,
        ] at this
        try simp only [fin_vals, Nat.reduceAdd] at h_lookup_row
        rewrite [←this, h_lookup_row.2]
        simp"

    open Lean Parser
    set_option hygiene false in
    elab "#register_chi_base" idx:num i: num out_cell:num in_cell1:num in_cell2:num in_cell3:num : command => do
      let returnType : String := returnTypeOfParams out_cell.getNat in_cell1.getNat in_cell2.getNat in_cell3.getNat
      let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the returnType."
      let tRtStx : TSyntax `term := ⟨rtStx⟩

      let proof := proofOfParams idx.getNat i.getNat in_cell1.getNat in_cell2.getNat in_cell3.getNat
      let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
      let tProofStx : TSyntax `term := ⟨proofStx⟩

      let uniqueName := mkIdent (Name.mkSimple s!"chi_base_{idx.getNat}_{i.getNat}")
      -- logInfo m!"Registering: {uniqueName}"
      Lean.Elab.Command.elabCommand
        (←`(lemma $uniqueName {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: 2^(4*BIT_COUNT) < P)
          (h_row: row < 730)
          (h_1: (c.get_advice $in_cell1 row).val = Normalize.normalize_unpacked x0 4)
          (h_2: (c.get_advice $in_cell2 row).val = Normalize.normalize_unpacked x1 4)
          (h_3: (c.get_advice $in_cell3 row).val = Normalize.normalize_unpacked x2 4): $tRtStx := $tProofStx))

  end ChiBase

  #register_chi_base 0 0 105 70 71 72
  #register_chi_base 0 1 106 71 72 73
  #register_chi_base 0 2 107 72 73 74
  #register_chi_base 0 3 108 73 74 70
  #register_chi_base 0 4 109 74 70 71
  #register_chi_base 1 0 110 75 76 77
  #register_chi_base 1 1 111 76 77 78
  #register_chi_base 1 2 112 77 78 79
  #register_chi_base 1 3 113 78 79 75
  #register_chi_base 1 4 114 79 75 76
  #register_chi_base 2 0 115 80 81 82
  #register_chi_base 2 1 116 81 82 83
  #register_chi_base 2 2 117 82 83 84
  #register_chi_base 2 3 118 83 84 80
  #register_chi_base 2 4 119 84 80 81
  #register_chi_base 3 0 120 85 86 87
  #register_chi_base 3 1 121 86 87 88
  #register_chi_base 3 2 122 87 88 89
  #register_chi_base 3 3 123 88 89 85
  #register_chi_base 3 4 124 89 85 86
  #register_chi_base 4 0 125 90 91 92
  #register_chi_base 4 1 126 91 92 93
  #register_chi_base 4 2 127 92 93 94
  #register_chi_base 4 3 128 93 94 90
  #register_chi_base 4 4 129 94 90 91
  #register_chi_base 5 0 130 95 96 97
  #register_chi_base 5 1 131 96 97 98
  #register_chi_base 5 2 132 97 98 99
  #register_chi_base 5 3 133 98 99 95
  #register_chi_base 5 4 134 99 95 96
  #register_chi_base 6 0 135 100 101 102
  #register_chi_base 6 1 136 101 102 103
  #register_chi_base 6 2 137 102 103 104
  #register_chi_base 6 3 138 103 104 100
  #register_chi_base 6 4 139 104 100 101

end Keccak.Soundness

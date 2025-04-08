import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness
  namespace SeparateDecodes
    def returnTypeOfParams (shift : ℕ) := s!"
      (x0 <<< {shift} ^^^ x1 <<< {shift} &&& x2 <<< {shift}) +
      (x3 ^^^ x4 &&& x5) =
      (x0 <<< {shift} + x3) ^^^ (x1 <<< {shift} + x4) &&& (x2 <<< {shift} + x5)
    "

    def proofOfParams (shift : ℕ) :=
      s!"by
        simp_all
        rewrite [show x0 = (BitVec.ofNat 12 x0).toNat by simp [Nat.mod_eq_of_lt h_x0]]
        rewrite [show x1 = (BitVec.ofNat 12 x1).toNat by simp [Nat.mod_eq_of_lt h_x1]]
        rewrite [show x2 = (BitVec.ofNat 12 x2).toNat by simp [Nat.mod_eq_of_lt h_x2]]
        rewrite [show x3 = (BitVec.ofNat {shift} x3).toNat by simp [Nat.mod_eq_of_lt h_x3]]
        rewrite [show x4 = (BitVec.ofNat {shift} x4).toNat by simp [Nat.mod_eq_of_lt h_x4]]
        rewrite [show x5 = (BitVec.ofNat {shift} x5).toNat by simp [Nat.mod_eq_of_lt h_x5]]
        rewrite [
          bitvec_toNat_shift_add {shift+12} (h := by trivial),
          bitvec_toNat_shift_add {shift+12} (h := by trivial),
          bitvec_toNat_shift_add {shift+12} (h := by trivial),
          ←BitVec.toNat_and, ←BitVec.toNat_and,
          ←BitVec.toNat_xor, ←BitVec.toNat_xor,
          ←bitvec_setWidth_shift_toNat (show 12 + {shift} ≤ {shift+12} by trivial),
          ←bitvec_setWidth_shift_toNat (show 12 + {shift} ≤ {shift+12} by trivial),
          ←bitvec_setWidth_shift_toNat (show 12 + {shift} ≤ {shift+12} by trivial),
          ←BitVec.toNat_and,
          ←BitVec.toNat_xor,
          ←bitvec_setWidth_toNat (width1 := {shift}) (width2 := {shift+12}) (h_width := by trivial),
          ←BitVec.toNat_add_of_lt
        ]
        . congr 1
          bv_decide
        . simp
          rewrite [
            Nat.mod_eq_of_lt h_x0,
            Nat.mod_eq_of_lt h_x1,
            Nat.mod_eq_of_lt h_x2,
            Nat.mod_eq_of_lt h_x3,
            Nat.mod_eq_of_lt h_x4,
            Nat.mod_eq_of_lt h_x5,
            Nat.mod_eq_of_lt (lt_trans h_x0 (by trivial)),
            Nat.mod_eq_of_lt (lt_trans h_x1 (by trivial)),
            Nat.mod_eq_of_lt (lt_trans h_x2 (by trivial)),
            Nat.mod_eq_of_lt (lt_trans h_x3 (by trivial)),
            Nat.mod_eq_of_lt (lt_trans h_x4 (by trivial)),
            Nat.mod_eq_of_lt (lt_trans h_x5 (by trivial)),
            Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega),
            ←Nat.shiftLeft_and_distrib,
            ←Nat.shiftLeft_xor_distrib
          ]
          have : x3 ^^^ x4 &&& x5 < 2^{shift} := by
            apply Nat.xor_lt_two_pow
            . omega
            . have := Nat.and_le_right (n := x4) (m := x5)
              omega
          have : x0 ^^^ x1 &&& x2 < 2^12 := by
            apply Nat.xor_lt_two_pow (n := 12)
            . omega
            . have := Nat.and_le_right (n := x1) (m := x2)
              omega
          omega"

    open Lean Parser
    set_option hygiene false in
    elab "#register_separate_decodes" shift:num : command => do
      let returnType : String := returnTypeOfParams shift.getNat
      let .ok rtStx := runParserCategory (← getEnv) `term returnType | throwError "Failed to parse the returnType."
      let tRtStx : TSyntax `term := ⟨rtStx⟩

      let proof := proofOfParams shift.getNat
      let .ok proofStx := runParserCategory (← getEnv) `term proof | throwError "Failed to parse the proof."
      let tProofStx : TSyntax `term := ⟨proofStx⟩

      let uniqueName := mkIdent (Name.mkSimple s!"separate_chi_decodes_{shift.getNat}")
      -- logInfo m!"Registering: {uniqueName}"
      Lean.Elab.Command.elabCommand
        (←`(lemma $uniqueName
          (h_x0: x0 < 2^12)
          (h_x1: x1 < 2^12)
          (h_x2: x2 < 2^12)
          (h_x3: x3 < 2^$shift)
          (h_x4: x4 < 2^$shift)
          (h_x5: x5 < 2^$shift)
        : $tRtStx := $tProofStx))
  end SeparateDecodes

  #register_separate_decodes 12
  #register_separate_decodes 24
  #register_separate_decodes 36
  #register_separate_decodes 48
  #register_separate_decodes 60
  #register_separate_decodes 72
  #register_separate_decodes 84
  #register_separate_decodes 96
  #register_separate_decodes 108
  #register_separate_decodes 120
  #register_separate_decodes 132
  #register_separate_decodes 144
  #register_separate_decodes 156
  #register_separate_decodes 168
  #register_separate_decodes 180

  lemma separate_chi_decodes_24_lt :
    Normalize.normalize_unpacked x1 4 <<< 12 +
    Normalize.normalize_unpacked x2 4 < 2^24
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    omega

  lemma separate_chi_decodes_36_lt :
    Normalize.normalize_unpacked x1 4 <<< 24 +
    (Normalize.normalize_unpacked x2 4 <<< 12 +
    Normalize.normalize_unpacked x3 4) < 2^36
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    omega

  lemma separate_chi_decodes_48_lt :
    Normalize.normalize_unpacked x1 4 <<< 36 +
    (Normalize.normalize_unpacked x2 4 <<< 24 +
    (Normalize.normalize_unpacked x3 4 <<< 12 +
    Normalize.normalize_unpacked x4 4)) < 2^48
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    omega

  lemma separate_chi_decodes_60_lt :
    Normalize.normalize_unpacked x1 4 <<< 48 +
    (Normalize.normalize_unpacked x2 4 <<< 36 +
    (Normalize.normalize_unpacked x3 4 <<< 24 +
    (Normalize.normalize_unpacked x4 4 <<< 12 +
    Normalize.normalize_unpacked x5 4))) < 2^60
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    omega


  lemma separate_chi_decodes_72_lt :
    Normalize.normalize_unpacked x1 4 <<< 60 +
    (Normalize.normalize_unpacked x2 4 <<< 48 +
    (Normalize.normalize_unpacked x3 4 <<< 36 +
    (Normalize.normalize_unpacked x4 4 <<< 24 +
    (Normalize.normalize_unpacked x5 4 <<< 12 +
    Normalize.normalize_unpacked x6 4)))) < 2^72
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    omega

  lemma separate_chi_decodes_84_lt :
    Normalize.normalize_unpacked x1 4 <<< 72 +
    (Normalize.normalize_unpacked x2 4 <<< 60 +
    (Normalize.normalize_unpacked x3 4 <<< 48 +
    (Normalize.normalize_unpacked x4 4 <<< 36 +
    (Normalize.normalize_unpacked x5 4 <<< 24 +
    (Normalize.normalize_unpacked x6 4 <<< 12 +
    Normalize.normalize_unpacked x7 4))))) < 2^84
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    omega

  lemma separate_chi_decodes_96_lt :
    Normalize.normalize_unpacked x1 4 <<< 84 +
    (Normalize.normalize_unpacked x2 4 <<< 72 +
    (Normalize.normalize_unpacked x3 4 <<< 60 +
    (Normalize.normalize_unpacked x4 4 <<< 48 +
    (Normalize.normalize_unpacked x5 4 <<< 36 +
    (Normalize.normalize_unpacked x6 4 <<< 24 +
    (Normalize.normalize_unpacked x7 4 <<< 12 +
    Normalize.normalize_unpacked x8 4)))))) < 2^96
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    omega

  lemma separate_chi_decodes_108_lt :
    Normalize.normalize_unpacked x1 4 <<< 96 +
    (Normalize.normalize_unpacked x2 4 <<< 84 +
    (Normalize.normalize_unpacked x3 4 <<< 72 +
    (Normalize.normalize_unpacked x4 4 <<< 60 +
    (Normalize.normalize_unpacked x5 4 <<< 48 +
    (Normalize.normalize_unpacked x6 4 <<< 36 +
    (Normalize.normalize_unpacked x7 4 <<< 24 +
    (Normalize.normalize_unpacked x8 4 <<< 12 +
    Normalize.normalize_unpacked x9 4))))))) < 2^108
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    omega

  lemma separate_chi_decodes_120_lt :
    Normalize.normalize_unpacked x1 4 <<< 108 +
    (Normalize.normalize_unpacked x2 4 <<< 96 +
    (Normalize.normalize_unpacked x3 4 <<< 84 +
    (Normalize.normalize_unpacked x4 4 <<< 72 +
    (Normalize.normalize_unpacked x5 4 <<< 60 +
    (Normalize.normalize_unpacked x6 4 <<< 48 +
    (Normalize.normalize_unpacked x7 4 <<< 36 +
    (Normalize.normalize_unpacked x8 4 <<< 24 +
    (Normalize.normalize_unpacked x9 4 <<< 12 +
    Normalize.normalize_unpacked x10 4)))))))) < 2^120
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    omega

  lemma separate_chi_decodes_132_lt :
    Normalize.normalize_unpacked x1 4 <<< 120 +
    (Normalize.normalize_unpacked x2 4 <<< 108 +
    (Normalize.normalize_unpacked x3 4 <<< 96 +
    (Normalize.normalize_unpacked x4 4 <<< 84 +
    (Normalize.normalize_unpacked x5 4 <<< 72 +
    (Normalize.normalize_unpacked x6 4 <<< 60 +
    (Normalize.normalize_unpacked x7 4 <<< 48 +
    (Normalize.normalize_unpacked x8 4 <<< 36 +
    (Normalize.normalize_unpacked x9 4 <<< 24 +
    (Normalize.normalize_unpacked x10 4 <<< 12 +
    Normalize.normalize_unpacked x11 4))))))))) < 2^132
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    omega

  lemma separate_chi_decodes_144_lt :
    Normalize.normalize_unpacked x1 4 <<< 132 +
    (Normalize.normalize_unpacked x2 4 <<< 120 +
    (Normalize.normalize_unpacked x3 4 <<< 108 +
    (Normalize.normalize_unpacked x4 4 <<< 96 +
    (Normalize.normalize_unpacked x5 4 <<< 84 +
    (Normalize.normalize_unpacked x6 4 <<< 72 +
    (Normalize.normalize_unpacked x7 4 <<< 60 +
    (Normalize.normalize_unpacked x8 4 <<< 48 +
    (Normalize.normalize_unpacked x9 4 <<< 36 +
    (Normalize.normalize_unpacked x10 4 <<< 24 +
    (Normalize.normalize_unpacked x11 4 <<< 12 +
    Normalize.normalize_unpacked x12 4)))))))))) < 2^144
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    omega

  lemma separate_chi_decodes_156_lt :
    Normalize.normalize_unpacked x1 4 <<< 144 +
    (Normalize.normalize_unpacked x2 4 <<< 132 +
    (Normalize.normalize_unpacked x3 4 <<< 120 +
    (Normalize.normalize_unpacked x4 4 <<< 108 +
    (Normalize.normalize_unpacked x5 4 <<< 96 +
    (Normalize.normalize_unpacked x6 4 <<< 84 +
    (Normalize.normalize_unpacked x7 4 <<< 72 +
    (Normalize.normalize_unpacked x8 4 <<< 60 +
    (Normalize.normalize_unpacked x9 4 <<< 48 +
    (Normalize.normalize_unpacked x10 4 <<< 36 +
    (Normalize.normalize_unpacked x11 4 <<< 24 +
    (Normalize.normalize_unpacked x12 4 <<< 12 +
    Normalize.normalize_unpacked x13 4))))))))))) < 2^156
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    have := Normalize.normalize_unpacked_4_le (x := x13)
    omega

  lemma separate_chi_decodes_168_lt :
    Normalize.normalize_unpacked x1 4 <<< 156 +
    (Normalize.normalize_unpacked x2 4 <<< 144 +
    (Normalize.normalize_unpacked x3 4 <<< 132 +
    (Normalize.normalize_unpacked x4 4 <<< 120 +
    (Normalize.normalize_unpacked x5 4 <<< 108 +
    (Normalize.normalize_unpacked x6 4 <<< 96 +
    (Normalize.normalize_unpacked x7 4 <<< 84 +
    (Normalize.normalize_unpacked x8 4 <<< 72 +
    (Normalize.normalize_unpacked x9 4 <<< 60 +
    (Normalize.normalize_unpacked x10 4 <<< 48 +
    (Normalize.normalize_unpacked x11 4 <<< 36 +
    (Normalize.normalize_unpacked x12 4 <<< 24 +
    (Normalize.normalize_unpacked x13 4 <<< 12 +
    Normalize.normalize_unpacked x14 4)))))))))))) < 2^168
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    have := Normalize.normalize_unpacked_4_le (x := x13)
    have := Normalize.normalize_unpacked_4_le (x := x14)
    omega

  lemma separate_chi_decodes_180_lt :
    Normalize.normalize_unpacked x1 4 <<< 168 +
    (Normalize.normalize_unpacked x2 4 <<< 156 +
    (Normalize.normalize_unpacked x3 4 <<< 144 +
    (Normalize.normalize_unpacked x4 4 <<< 132 +
    (Normalize.normalize_unpacked x5 4 <<< 120 +
    (Normalize.normalize_unpacked x6 4 <<< 108 +
    (Normalize.normalize_unpacked x7 4 <<< 96 +
    (Normalize.normalize_unpacked x8 4 <<< 84 +
    (Normalize.normalize_unpacked x9 4 <<< 72 +
    (Normalize.normalize_unpacked x10 4 <<< 60 +
    (Normalize.normalize_unpacked x11 4 <<< 48 +
    (Normalize.normalize_unpacked x12 4 <<< 36 +
    (Normalize.normalize_unpacked x13 4 <<< 24 +
    (Normalize.normalize_unpacked x14 4 <<< 12 +
    Normalize.normalize_unpacked x15 4))))))))))))) < 2^180
  := by
    have := Normalize.normalize_unpacked_4_le (x := x1)
    have := Normalize.normalize_unpacked_4_le (x := x2)
    have := Normalize.normalize_unpacked_4_le (x := x3)
    have := Normalize.normalize_unpacked_4_le (x := x4)
    have := Normalize.normalize_unpacked_4_le (x := x5)
    have := Normalize.normalize_unpacked_4_le (x := x6)
    have := Normalize.normalize_unpacked_4_le (x := x7)
    have := Normalize.normalize_unpacked_4_le (x := x8)
    have := Normalize.normalize_unpacked_4_le (x := x9)
    have := Normalize.normalize_unpacked_4_le (x := x10)
    have := Normalize.normalize_unpacked_4_le (x := x11)
    have := Normalize.normalize_unpacked_4_le (x := x12)
    have := Normalize.normalize_unpacked_4_le (x := x13)
    have := Normalize.normalize_unpacked_4_le (x := x14)
    have := Normalize.normalize_unpacked_4_le (x := x15)
    omega

end Keccak.Soundness

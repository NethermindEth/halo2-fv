import Examples.Scroll.Keccak.Soundness.Sequencing.Iota
import Examples.Scroll.Keccak.Soundness.Sequencing.RhoEquiv
import Examples.Scroll.Keccak.Soundness.Sequencing.Util
import Examples.Scroll.Keccak.Soundness.Iota
import Examples.Scroll.Keccak.Soundness.Rho
import Examples.Scroll.Keccak.Soundness.Theta

namespace Keccak.Soundness

  lemma iota_s_0_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 0 0).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[0]?.map UInt64_to_unpacked_Nat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_0 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
      ZMod.val_add,
      UInt64_to_unpacked_Nat_xor
    ]
    have h_normalize_le (x) := Normalize.normalize_unpacked_64_le_mask (x := x)
    unfold Normalize.mask at h_normalize_le
    rewrite [
      Nat.mod_eq_of_lt (lt_of_le_of_lt (h_normalize_le _) (by omega))
    ]
    rewrite [
      add_comm,
      chi_os'_0_0 h_meets_constraints h_round' (by omega),
      ←Normalize.normalize_unpacked_UInt64,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (add_le_add (h_normalize_le _) (h_normalize_le _)) (by omega)),
      Normalize.normalize_unpacked_add_eq_xor,
      Normalize.normalize_unpacked_xor,
    ]
    apply congr_xor
    . rw [
        Normalize.normalize_unpacked_UInt64,
        Array.getElem_eq_getElem?_get,
        Option.get_eq_getD,
        Array.getElem!_eq_getD,
        Array.getD_eq_getD_getElem?,
      ]
    . rw [
        Normalize.normalize_unpacked_xor,
        Normalize.normalize_unpacked_and,
        UInt64_to_unpacked_Nat_and,
        uint64_to_unpacked_nat_complement,
        ←rho_s_0_0_equiv
          h_meets_constraints
          h_round'
          h_P
          h_s_0_0
          h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
          h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
        ←rho_s_1_1_equiv
          h_meets_constraints
          h_round'
          h_P
          h_s_1_1
          h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
          h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
        normalize_bit_invert_normalize_64,
        ←rho_s_2_2_equiv
          h_meets_constraints
          h_round'
          h_P
          h_s_2_2
          h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
          h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      ]

  lemma iota_s_0_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 0 1).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[1]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_1 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_0_1 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_3_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_0
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_4_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_1
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_0_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma iota_s_0_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 0 2).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[2]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_2 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_0_2 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_1_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_0
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      ←rho_s_2_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_3_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_2
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_0_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 0 3).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[3]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_3 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_0_3 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_4_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_0
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      ←rho_s_0_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_1_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_2
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
    ]

  lemma iota_s_0_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 0 4).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[4]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_4 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_0_4 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_2_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      ←rho_s_3_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_1
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_4_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_2
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
    ]

  lemma iota_s_1_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 1 0).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[5]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_5 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_1_0 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_1_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_1
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      ←rho_s_2_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_3_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_3
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_1_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 1 1).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[6]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_6 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_1_1 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_4_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_1
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      ←rho_s_0_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_1_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_3
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
    ]

  lemma iota_s_1_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 1 2).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[7]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_7 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_1_2 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_2_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      ←rho_s_3_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_2
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_4_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_3
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
    ]

  lemma iota_s_1_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 1 3).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[8]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_8 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_1_3 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_0_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_1_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_2
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_2_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
    ]

  lemma iota_s_1_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 1 4).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[9]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_9 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_1_4 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_3_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_1
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_4_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_2
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_0_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_2_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 2 0).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[10]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_10 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_2_0 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_2_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      ←rho_s_3_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_3
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_4_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
    ]

  lemma iota_s_2_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 2 1).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[11]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_11 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_2_1 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_0_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_1_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_3
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_2_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
    ]

  lemma iota_s_2_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 2 2).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[12]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_12 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_2_2 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_3_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_2
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_4_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_3
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_0_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_2_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 2 3).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[13]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_13 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_2_3 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_1_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_2
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      ←rho_s_2_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_3_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_2_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 2 4).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[14]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_14 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_2_4 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_4_2_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_2
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      ←rho_s_0_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_1_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
    ]

  lemma iota_s_3_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 3 0).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[15]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_15 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_3_0 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_3_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_3
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_4_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_0_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_3_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 3 1).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[16]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_16 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_3_1 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_1_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_3
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      ←rho_s_2_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_3_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_0
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_3_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 3 2).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[17]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_17 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_3_2 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_4_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_3
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      ←rho_s_0_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_1_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_0
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
    ]

  lemma iota_s_3_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 3 3).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[18]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_18 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_3_3 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_2_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      ←rho_s_3_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_4_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_0
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
    ]

  lemma iota_s_3_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 3 4).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[19]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_19 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_3_4 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_0_3_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_1_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_2_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
    ]

  lemma iota_s_4_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 4 0).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[20]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_20 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_4_0 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_4_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      ←rho_s_0_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_1_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_1
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
    ]

  lemma iota_s_4_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 4 1).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[21]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_21 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_4_1 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_2_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      ←rho_s_3_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_0
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_4_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_1
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
    ]

  lemma iota_s_4_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 4 2).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[22]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_22 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_4_2 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_0_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_1_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_0
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_2_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
    ]

  lemma iota_s_4_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 4 3).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[23]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_23 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_4_3 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_3_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
      ←rho_s_4_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_4_0
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_0_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_0_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_4_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) 4 4).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[24]?.map UInt64_to_unpacked_Nat
  := by
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_24 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
    ]
    rw [
      chi_os'_4_4 h_meets_constraints h_round' (by omega),
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_and,
      UInt64_to_unpacked_Nat_xor,
      UInt64_to_unpacked_Nat_and,
      uint64_to_unpacked_nat_complement,
      ←rho_s_1_4_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_1_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4,
      ←rho_s_2_0_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_2_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4,
      normalize_bit_invert_normalize_64,
      ←rho_s_3_1_equiv
        h_meets_constraints
        h_round'
        h_P
        h_s_3_1
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4,
    ]

  lemma iota_s_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 0 23)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c (round+1) 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c (round+1) 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c (round+1) 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c (round+1) 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c (round+1) 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c (round+1) 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c (round+1) 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c (round+1) 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c (round+1) 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c (round+1) 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c (round+1) 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c (round+1) 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c (round+1) 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c (round+1) 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c (round+1) 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c (round+1) 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c (round+1) 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c (round+1) 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c (round+1) 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c (round+1) 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c (round+1) 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c (round+1) 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c (round+1) 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c (round+1) 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c (round+1) 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c (round+1) y x).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[y.val*5+x.val]?.map UInt64_to_unpacked_Nat
  := by
    fin_cases y <;> fin_cases x
    . exact iota_s_0_0_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_0_1_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_0_2_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_0_3_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_0_4_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_1_0_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_1_1_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_1_2_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_1_3_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_1_4_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_2_0_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_2_1_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_2_2_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_2_3_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_2_4_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_3_0_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_3_1_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_3_2_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_3_3_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_3_4_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_4_0_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_4_1_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_4_2_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_4_3_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    . exact iota_s_4_4_equiv h_meets_constraints h_round h_P h_state
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4




end Keccak.Soundness

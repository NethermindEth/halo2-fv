import Examples.Scroll.Keccak.Soundness.Sequencing.Rho
import Examples.Scroll.Keccak.Soundness.Sequencing.ThetaEquiv
import Examples.Scroll.Keccak.Soundness.Sequencing.Util

namespace Keccak.Soundness

  lemma rho_s_0_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_0_0 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x0 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 0
    )
  := by
    rewrite [
      rho_s_0_0_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_0,
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_0,
      theta_os_0_0_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_0_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_0_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_0_1 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x1 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 36
    )
  := by
    rewrite [
      rho_s_0_1_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_36,
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_108,
      theta_os_0_1_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_0_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_0_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_0_2 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x2 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 3
    )
  := by
    rewrite [
      rho_s_0_2_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_3,
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_9,
      theta_os_0_2_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_0_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_0_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_0_3 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x3 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 41
    )
  := by
    rewrite [
      rho_s_0_3_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_41,
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_123,
      theta_os_0_3_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_0_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_0_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_0_4 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x4 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 18
    )
  := by
    rewrite [
      rho_s_0_4_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_18,
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_54,
      theta_os_0_4_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_0_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_1_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14):
    Normalize.normalize_unpacked (rho_s_1_0 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x5 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 1
    )
  := by
    rewrite [
      rho_s_1_0_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_1
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_3,
      theta_os_1_0_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_1_0
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
    ]

  lemma rho_s_1_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14):
    Normalize.normalize_unpacked (rho_s_1_1 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x6 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 44
    )
  := by
    rewrite [
      rho_s_1_1_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_44
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_132,
      theta_os_1_1_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_1_1
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
    ]

  lemma rho_s_1_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14):
    Normalize.normalize_unpacked (rho_s_1_2 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x7 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 10
    )
  := by
    rewrite [
      rho_s_1_2_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_10
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_30,
      theta_os_1_2_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_1_2
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
    ]

  lemma rho_s_1_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14):
    Normalize.normalize_unpacked (rho_s_1_3 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x8 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 45
    )
  := by
    rewrite [
      rho_s_1_3_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_45
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_135,
      theta_os_1_3_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_1_3
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
    ]

  lemma rho_s_1_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14):
    Normalize.normalize_unpacked (rho_s_1_4 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x9 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 2
    )
  := by
    rewrite [
      rho_s_1_4_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_2
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_6,
      theta_os_1_4_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_1_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
    ]

  lemma rho_s_2_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19):
    Normalize.normalize_unpacked (rho_s_2_0 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x10 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 62
    )
  := by
    rewrite [
      rho_s_2_0_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_62
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_186,
      theta_os_2_0_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_2_0
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
    ]

  lemma rho_s_2_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19):
    Normalize.normalize_unpacked (rho_s_2_1 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x11 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 6
    )
  := by
    rewrite [
      rho_s_2_1_rotation h_meets_constraints h_round (by omega),
      rotate_to_unpacked_nat_6
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_18,
      theta_os_2_1_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_2_1
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
    ]

  lemma rho_s_2_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19):
    Normalize.normalize_unpacked (rho_s_2_2 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x12 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 43
    )
  := by
    rewrite [
      rho_s_2_2_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_43
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_129,
      theta_os_2_2_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_2_2
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
    ]

  lemma rho_s_2_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19):
    Normalize.normalize_unpacked (rho_s_2_3 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x13 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 15
    )
  := by
    rewrite [
      rho_s_2_3_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_15
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_45,
      theta_os_2_3_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_2_3
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
    ]

  lemma rho_s_2_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_1_0: (s c round 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c round 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c round 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c round 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c round 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19):
    Normalize.normalize_unpacked (rho_s_2_4 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x14 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 61
    )
  := by
    rewrite [
      rho_s_2_4_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_61
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_183,
      theta_os_2_4_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_2_4
        h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
    ]

  lemma rho_s_3_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_3_0 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x15 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 28
    )
  := by
    rewrite [
      rho_s_3_0_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_28
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_84,
      theta_os_3_0_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_3_0
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_3_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_3_1 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x16 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 55
    )
  := by
    rewrite [
      rho_s_3_1_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_55
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_165,
      theta_os_3_1_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_3_1
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_3_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_3_2 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x17 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 25
    )
  := by
    rewrite [
      rho_s_3_2_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_25
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_75,
      theta_os_3_2_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_3_2
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_3_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_3_3 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x18 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 21
    )
  := by
    rewrite [
      rho_s_3_3_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_21
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_63,
      theta_os_3_3_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_3_3
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_3_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_2_0: (s c round 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c round 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c round 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c round 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c round 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24):
    Normalize.normalize_unpacked (rho_s_3_4 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x19 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 56
    )
  := by
    rewrite [
      rho_s_3_4_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_56
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_168,
      theta_os_3_4_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_3_4
        h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
        h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    ]

  lemma rho_s_4_0_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_4_0: (s c round 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4):
    Normalize.normalize_unpacked (rho_s_4_0 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x20 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 27
    )
  := by
    rewrite [
      rho_s_4_0_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_27
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_81,
      theta_os_4_0_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_4_0
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
    ]

  lemma rho_s_4_1_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_4_1: (s c round 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4):
    Normalize.normalize_unpacked (rho_s_4_1 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x21 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 20
    )
  := by
    rewrite [
      rho_s_4_1_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_20
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_60,
      theta_os_4_1_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_4_1
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
    ]

  lemma rho_s_4_2_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_4_2: (s c round 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4):
    Normalize.normalize_unpacked (rho_s_4_2 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x22 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 39
    )
  := by
    rewrite [
      rho_s_4_2_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_39
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_117,
      theta_os_4_2_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_4_2
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
    ]

  lemma rho_s_4_3_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_4_3: (s c round 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4):
    Normalize.normalize_unpacked (rho_s_4_3 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x23 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 8
    )
  := by
    rewrite [
      rho_s_4_3_rotation h_meets_constraints h_round (by unfold Normalize.mask; omega),
      rotate_to_unpacked_nat_8
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_24,
      theta_os_4_3_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_4_3
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
    ]

  lemma rho_s_4_4_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_round: round ∈ Finset.Icc 1 24)
    (h_P: 2^200 ≤ P)
    (h_s_4_4: (s c round 4 4).val = UInt64_to_unpacked_Nat x24)
    (h_s_3_0: (s c round 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c round 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c round 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c round 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c round 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_0_0: (s c round 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c round 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c round 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c round 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c round 0 4).val = UInt64_to_unpacked_Nat x4):
    Normalize.normalize_unpacked (rho_s_4_4 c round) 64 =
    UInt64_to_unpacked_Nat (
      LeanCrypto.rotateL (x24 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 14
    )
  := by
    rewrite [
      rho_s_4_4_rotation h_meets_constraints h_round h_P,
      rotate_to_unpacked_nat_14
    ]
    simp only [keccak_constants, Nat.reduceMul]
    rw [
      ←rotate_normalized_42,
      theta_os_4_4_equiv
        h_meets_constraints
        h_round
        h_P
        h_s_4_4
        h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
        h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
    ]

end Keccak.Soundness

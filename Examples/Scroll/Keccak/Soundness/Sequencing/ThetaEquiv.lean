import Examples.Scroll.Keccak.Soundness.Sequencing.Util
import Examples.Scroll.Keccak.Soundness.Theta

namespace Keccak.Soundness

  lemma theta_os_0_0_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 0 0).val 64 =
    (UInt64_to_unpacked_Nat
            (x0 ^^^
              (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^
                LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)))
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_0_0,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x0),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_0_1_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 0 1).val 64 =
    (UInt64_to_unpacked_Nat
            (x1 ^^^
              (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^
                LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)))
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_0_1,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x1),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_0_2_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 0 2).val 64 =
    (UInt64_to_unpacked_Nat
            (x2 ^^^
              (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^
                LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)))
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_0_2,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x2),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_0_3_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 0 3).val 64 =
    (UInt64_to_unpacked_Nat
            (x3 ^^^
              (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^
                LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)))
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_0_3,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x3),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_0_4_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 0 4).val 64 =
    (UInt64_to_unpacked_Nat
            (x4 ^^^
              (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^
                LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)))
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_0_4,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x4),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_1_0_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 1 0).val 64 =
    (UInt64_to_unpacked_Nat
      (x5 ^^^
        (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^
          LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_1_0,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x5),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_1_1_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 1 1).val 64 =
    (UInt64_to_unpacked_Nat
      (x6 ^^^
        (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^
          LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_1_1,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x6),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_1_2_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 1 2).val 64 =
    (UInt64_to_unpacked_Nat
      (x7 ^^^
        (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^
          LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_1_2,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x7),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_1_3_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 1 3).val 64 =
    (UInt64_to_unpacked_Nat
      (x8 ^^^
        (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^
          LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_1_3,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x8),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_1_4_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 1 4).val 64 =
    (UInt64_to_unpacked_Nat
      (x9 ^^^
        (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^
          LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_1_4,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x9),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_2_0_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 2 0).val 64 =
    (UInt64_to_unpacked_Nat
      (x10 ^^^
        (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^
        LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_2_0,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x10),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_2_1_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 2 1).val 64 =
    (UInt64_to_unpacked_Nat
      (x11 ^^^
        (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^
        LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_2_1,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x11),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_2_2_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 2 2).val 64 =
    (UInt64_to_unpacked_Nat
      (x12 ^^^
        (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^
        LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_2_2,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x12),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_2_3_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 2 3).val 64 =
    (UInt64_to_unpacked_Nat
      (x13 ^^^
        (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^
        LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_2_3,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x13),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_2_4_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 2 4).val 64 =
    (UInt64_to_unpacked_Nat
      (x14 ^^^
        (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^
        LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_2_4,
      h_s_1_0, h_s_1_1, h_s_1_2, h_s_1_3, h_s_1_4,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x14),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_3_0_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 3 0).val 64 =
    (UInt64_to_unpacked_Nat
      (x15 ^^^
        (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^
        LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_3_0,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x15),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_3_1_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 3 1).val 64 =
    (UInt64_to_unpacked_Nat
      (x16 ^^^
        (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^
        LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_3_1,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x16),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_3_2_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 3 2).val 64 =
    (UInt64_to_unpacked_Nat
      (x17 ^^^
        (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^
        LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_3_2,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x17),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_3_3_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 3 3).val 64 =
    (UInt64_to_unpacked_Nat
      (x18 ^^^
        (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^
        LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_3_3,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x18),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_3_4_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 3 4).val 64 =
    (UInt64_to_unpacked_Nat
      (x19 ^^^
        (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^
        LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_3_4,
      h_s_2_0, h_s_2_1, h_s_2_2, h_s_2_3, h_s_2_4,
      h_s_4_0, h_s_4_1, h_s_4_2, h_s_4_3, h_s_4_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x19),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_4_0_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 4 0).val 64 =
    (UInt64_to_unpacked_Nat
      (x20 ^^^
        (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^
        LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_4_0,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x20),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_4_1_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 4 1).val 64 =
    (UInt64_to_unpacked_Nat
      (x21 ^^^
        (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^
        LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_4_1,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x21),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_4_2_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 4 2).val 64 =
    (UInt64_to_unpacked_Nat
      (x22 ^^^
        (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^
        LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_4_2,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x22),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_4_3_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 4 3).val 64 =
    (UInt64_to_unpacked_Nat
      (x23 ^^^
        (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^
        LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_4_3,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x23),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

  lemma theta_os_4_4_equiv {c: ValidCircuit P P_Prime}
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
    Normalize.normalize_unpacked (os c round 4 4).val 64 =
    (UInt64_to_unpacked_Nat
      (x24 ^^^
        (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^
        LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)
      )
    )
  := by
    simp only [
      os_theta h_meets_constraints h_round (by omega),
      Fin.reduceAdd, keccak_constants
    ]
    rewrite [
      h_s_4_4,
      h_s_3_0, h_s_3_1, h_s_3_2, h_s_3_3, h_s_3_4,
      h_s_0_0, h_s_0_1, h_s_0_2, h_s_0_3, h_s_0_4,
      normalize_uint64_add_add_add_add_eq_xor,
      normalize_uint64_add_add_add_add_eq_xor,
      rotate_normalized_3,
      ←Normalize.normalize_unpacked_UInt64 (x := x24),
      ←add_assoc,
      normalize_add_add_eq_xor,
    ]
    simp only [
      UInt64_to_unpacked_Nat_xor,
      Nat.xor_assoc,
      Normalize.normalize_unpacked_xor,
      rotate_to_unpacked_nat_1,
      keccak_constants,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_UInt64,
      rotate_uint64_xors_normalized_3
    ]

end Keccak.Soundness

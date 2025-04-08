import Examples.Scroll.Keccak.Soundness.Sequencing.Pi

namespace Keccak.Soundness

  lemma array_get! (a: Array UInt64) (x: ℕ) (h: a[x]? = .some data):
    a[x]! = data
  := by simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, h]


  lemma spec_chi_0 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[0]? =
    .some (LeanCrypto.rotateL
      (x0 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 0 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x6 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
          44) &&&
      LeanCrypto.rotateL
        (x12 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 43)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_0 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_5 h_state,
      spec_pi_10 h_state,
      array_get!
    ]

  lemma spec_chi_1 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[1]? =
    .some (LeanCrypto.rotateL
      (x15 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
      28 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x21 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
          20) &&&
      LeanCrypto.rotateL
        (x2 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 3)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_1 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_6 h_state,
      spec_pi_11 h_state,
      array_get!
    ]

  lemma spec_chi_2 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[2]? =
    .some (LeanCrypto.rotateL
      (x5 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 1 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x11 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
          6) &&&
      LeanCrypto.rotateL
        (x17 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
        25)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_2 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_7 h_state,
      spec_pi_12 h_state,
      array_get!
    ]

  lemma spec_chi_3 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[3]? =
    .some (LeanCrypto.rotateL
      (x20 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 27 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x1 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
          36) &&&
      LeanCrypto.rotateL
        (x7 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 10)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_3 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_8 h_state,
      spec_pi_13 h_state,
      array_get!
    ]

  lemma spec_chi_4 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[4]? =
    .some (LeanCrypto.rotateL
      (x10 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 62 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x16 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
          55) &&&
      LeanCrypto.rotateL
        (x22 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 39)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_4 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_9 h_state,
      spec_pi_14 h_state,
      array_get!
    ]

  lemma spec_chi_5 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[5]? =
    .some (LeanCrypto.rotateL
      (x6 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 44 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x12 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
          43) &&&
      LeanCrypto.rotateL
        (x18 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
        21)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_5 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_10 h_state,
      spec_pi_15 h_state,
      array_get!
    ]

  lemma spec_chi_6 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[6]? =
    .some (LeanCrypto.rotateL
      (x21 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 20 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x2 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
          3) &&&
      LeanCrypto.rotateL
        (x8 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 45)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_6 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_11 h_state,
      spec_pi_16 h_state,
      array_get!
    ]

  lemma spec_chi_7 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[7]? =
    .some (LeanCrypto.rotateL
      (x11 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 6 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x17 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
          25) &&&
      LeanCrypto.rotateL
        (x23 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 8)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_7 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_12 h_state,
      spec_pi_17 h_state,
      array_get!
    ]

  lemma spec_chi_8 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[8]? =
    .some (LeanCrypto.rotateL
      (x1 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 36 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x7 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
          10) &&&
      LeanCrypto.rotateL
        (x13 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 15)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_8 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_13 h_state,
      spec_pi_18 h_state,
      array_get!
    ]

  lemma spec_chi_9 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[9]? =
    .some (LeanCrypto.rotateL
      (x16 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
      55 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x22 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
          39) &&&
      LeanCrypto.rotateL
        (x3 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 41)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_9 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_14 h_state,
      spec_pi_19 h_state,
      array_get!
    ]

  lemma spec_chi_10 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[10]? =
    .some (LeanCrypto.rotateL
      (x12 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 43 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x18 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
          21) &&&
      LeanCrypto.rotateL
        (x24 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 14)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_10 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_15 h_state,
      spec_pi_20 h_state,
      array_get!
    ]

  lemma spec_chi_11 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[11]? =
    .some (LeanCrypto.rotateL
      (x2 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 3 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x8 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
          45) &&&
      LeanCrypto.rotateL
        (x14 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 61)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_11 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_16 h_state,
      spec_pi_21 h_state,
      array_get!
    ]

  lemma spec_chi_12 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[12]? =
    .some (LeanCrypto.rotateL
      (x17 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
      25 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x23 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
          8) &&&
      LeanCrypto.rotateL
        (x4 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 18)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_12 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_17 h_state,
      spec_pi_22 h_state,
      array_get!
    ]

  lemma spec_chi_13 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[13]? =
    .some (LeanCrypto.rotateL
      (x7 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 10 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x13 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
          15) &&&
      LeanCrypto.rotateL
        (x19 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
        56)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_13 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_18 h_state,
      spec_pi_23 h_state,
      array_get!
    ]

  lemma spec_chi_14 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[14]? =
    .some (LeanCrypto.rotateL
      (x22 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 39 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x3 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
          41) &&&
      LeanCrypto.rotateL
        (x9 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 2)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_14 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_19 h_state,
      spec_pi_24 h_state,
      array_get!
    ]

  lemma spec_chi_15 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[15]? =
    .some (LeanCrypto.rotateL
      (x18 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
      21 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x24 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
          14) &&&
      LeanCrypto.rotateL
        (x0 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 0)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_15 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_20 h_state,
      spec_pi_0 h_state,
      array_get!
    ]

  lemma spec_chi_16 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[16]? =
    .some (LeanCrypto.rotateL
      (x8 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 45 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x14 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
          61) &&&
      LeanCrypto.rotateL
        (x15 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
        28)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_16 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_21 h_state,
      spec_pi_1 h_state,
      array_get!
    ]

  lemma spec_chi_17 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[17]? =
    .some (LeanCrypto.rotateL
      (x23 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 8 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x4 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
          18) &&&
      LeanCrypto.rotateL
        (x5 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 1)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_17 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_22 h_state,
      spec_pi_2 h_state,
      array_get!
    ]

  lemma spec_chi_18 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[18]? =
    .some (LeanCrypto.rotateL
      (x13 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 15 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x19 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
          56) &&&
      LeanCrypto.rotateL
        (x20 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 27)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_18 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_23 h_state,
      spec_pi_3 h_state,
      array_get!
    ]

  lemma spec_chi_19 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[19]? =
    .some (LeanCrypto.rotateL
      (x3 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 41 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x9 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
          2) &&&
      LeanCrypto.rotateL
        (x10 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 62)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_19 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_24 h_state,
      spec_pi_4 h_state,
      array_get!
    ]

  lemma spec_chi_20 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[20]? =
    .some (LeanCrypto.rotateL
      (x24 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 14 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x0 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
          0) &&&
      LeanCrypto.rotateL
        (x6 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 44)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_20 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_0 h_state,
      spec_pi_5 h_state,
      array_get!
    ]

  lemma spec_chi_21 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[21]? =
    .some (LeanCrypto.rotateL
      (x14 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 61 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x15 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
          28) &&&
      LeanCrypto.rotateL
        (x21 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 20)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_21 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_1 h_state,
      spec_pi_6 h_state,
      array_get!
    ]

  lemma spec_chi_22 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[22]? =
    .some (LeanCrypto.rotateL
      (x4 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 18 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x5 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
          1) &&&
      LeanCrypto.rotateL
        (x11 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 6)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_22 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_2 h_state,
      spec_pi_7 h_state,
      array_get!
    ]

  lemma spec_chi_23 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[23]? =
    .some (LeanCrypto.rotateL
      (x19 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
      56 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x20 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
          27) &&&
      LeanCrypto.rotateL
        (x1 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 36)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_23 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_3 h_state,
      spec_pi_8 h_state,
      array_get!
    ]

  lemma spec_chi_24 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.χ
      (LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state)))
    )[24]? =
    .some (LeanCrypto.rotateL
      (x9 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 2 ^^^
    LeanCrypto.complement
        (LeanCrypto.rotateL
          (x10 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
          62) &&&
      LeanCrypto.rotateL
        (x16 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
        55)
  := by
    simp [
      LeanCrypto.HashFunctions.χ,
      spec_pi_24 h_state,
      LeanCrypto.HashFunctions.χ.subChi,
      spec_pi_4 h_state,
      spec_pi_9 h_state,
      array_get!
    ]
end Keccak.Soundness

import Examples.Scroll.Keccak.Soundness.Sequencing.Rho

namespace Keccak.Soundness

  lemma spec_pi_0 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[0]? =
    .some (LeanCrypto.rotateL (x0 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 0)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_0 h_state
    ]

  lemma spec_pi_1 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[1]? =
    .some (LeanCrypto.rotateL (x15 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 28)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_15 h_state
    ]

  lemma spec_pi_2 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[2]? =
    .some (LeanCrypto.rotateL (x5 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 1)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_5 h_state
    ]

  lemma spec_pi_3 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[3]? =
    .some (LeanCrypto.rotateL (x20 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 27)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_20 h_state
    ]

  lemma spec_pi_4 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[4]? =
    .some (LeanCrypto.rotateL (x10 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 62)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_10 h_state
    ]

  lemma spec_pi_5 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[5]? =
    .some (LeanCrypto.rotateL (x6 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 44)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_6 h_state
    ]

  lemma spec_pi_6 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[6]? =
    .some (LeanCrypto.rotateL (x21 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 20)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_21 h_state
    ]

  lemma spec_pi_7 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[7]? =
    .some (LeanCrypto.rotateL (x11 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 6)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_11 h_state
    ]

  lemma spec_pi_8 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[8]? =
    .some (LeanCrypto.rotateL (x1 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 36)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_1 h_state
    ]

  lemma spec_pi_9 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[9]? =
    .some (LeanCrypto.rotateL (x16 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 55)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_16 h_state
    ]

  lemma spec_pi_10 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[10]? =
    .some (LeanCrypto.rotateL (x12 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 43)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_12 h_state
    ]

  lemma spec_pi_11 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[11]? =
    .some (LeanCrypto.rotateL (x2 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 3)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_2 h_state
    ]

  lemma spec_pi_12 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[12]? =
    .some (LeanCrypto.rotateL (x17 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 25)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_17 h_state
    ]

  lemma spec_pi_13 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[13]? =
    .some (LeanCrypto.rotateL (x7 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 10)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_7 h_state
    ]

  lemma spec_pi_14 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[14]? =
    .some (LeanCrypto.rotateL (x22 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 39)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_22 h_state
    ]

  lemma spec_pi_15 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[15]? =
    .some (LeanCrypto.rotateL (x18 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 21)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_18 h_state
    ]

  lemma spec_pi_16 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[16]? =
    .some (LeanCrypto.rotateL (x8 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 45)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_8 h_state
    ]

  lemma spec_pi_17 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[17]? =
    .some (LeanCrypto.rotateL (x23 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 8)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_23 h_state
    ]

  lemma spec_pi_18 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[18]? =
    .some (LeanCrypto.rotateL (x13 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 15)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_13 h_state
    ]

  lemma spec_pi_19 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[19]? =
    .some (LeanCrypto.rotateL (x3 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 41)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_3 h_state
    ]

  lemma spec_pi_20 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[20]? =
    .some (LeanCrypto.rotateL (x24 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1)) 14)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_24 h_state
    ]

  lemma spec_pi_21 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[21]? =
    .some (LeanCrypto.rotateL (x14 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1)) 61)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_14 h_state
    ]

  lemma spec_pi_22 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[22]? =
    .some (LeanCrypto.rotateL (x4 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1)) 18)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_4 h_state
    ]

  lemma spec_pi_23 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[23]? =
    .some (LeanCrypto.rotateL (x19 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1)) 56)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_19 h_state
    ]

  lemma spec_pi_24 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (
      LeanCrypto.HashFunctions.π
      (LeanCrypto.HashFunctions.ρ
      (LeanCrypto.HashFunctions.θ state))
    )[24]? =
    .some (LeanCrypto.rotateL (x9 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1)) 2)
  := by
    simp [
      LeanCrypto.HashFunctions.π,
      Array.backpermute,
      LeanCrypto.HashFunctions.piConstants,
      spec_rho_9 h_state
    ]
end Keccak.Soundness

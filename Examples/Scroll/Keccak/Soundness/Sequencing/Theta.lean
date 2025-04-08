import Examples.Scroll.Keccak.Soundness.Theta

namespace Keccak.Soundness
  lemma spec_theta_0 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[0]? =
    .some (x0 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_1 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[1]? =
    .some (x1 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_2 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[2]? =
    .some (x2 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_3 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[3]? =
    .some (x3 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_4 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[4]? =
    .some (x4 ^^^ (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ LeanCrypto.rotateL (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_5 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[5]? =
    .some (x5 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_6 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[6]? =
    .some (x6 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_7 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[7]? =
    .some (x7 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_8 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[8]? =
    .some (x8 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_9 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[9]? =
    .some (x9 ^^^ (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ LeanCrypto.rotateL (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_10 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[10]? =
     .some (x10 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_11 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[11]? =
     .some (x11 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_12 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[12]? =
     .some (x12 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_13 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[13]? =
     .some (x13 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_14 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[14]? =
     .some (x14 ^^^ (x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ LeanCrypto.rotateL (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_15 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[15]? =
     .some (x15 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_16 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[16]? =
     .some (x16 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_17 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[17]? =
     .some (x17 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_18 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[18]? =
     .some (x18 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_19 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[19]? =
     .some (x19 ^^^ (x10 ^^^ x11 ^^^ x12 ^^^ x13 ^^^ x14 ^^^ LeanCrypto.rotateL (x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_20 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[20]? =
     .some (x20 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_21 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[21]? =
     .some (x21 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_22 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[22]? =
     .some (x22 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_23 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[23]? =
     .some (x23 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]

  lemma spec_theta_24 (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    (LeanCrypto.HashFunctions.θ state)[24]? =
     .some (x24 ^^^ (x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ LeanCrypto.rotateL (x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4) 1))
  := by
    simp [LeanCrypto.HashFunctions.θ, array_range_25, h_state]
    simp [LeanCrypto.HashFunctions.θ.d]
    simp [LeanCrypto.HashFunctions.θ.c, array_range_5]
    simp [Array.foldl1]
end Keccak.Soundness

import Examples.Scroll.Keccak.Soundness.Sequencing.IotaEquiv

namespace Keccak.Soundness

  lemma array_size_25:
    #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24].size = 25
  := by aesop

  lemma array_ext_25 {array: Array T} (h: array.size = 25):
    array = #[
      array[0], array[1], array[2], array[3], array[4],
      array[5], array[6], array[7], array[8], array[9],
      array[10], array[11], array[12], array[13], array[14],
      array[15], array[16], array[17], array[18], array[19],
      array[20], array[21], array[22], array[23], array[24]
    ]
  := by
    apply Array.ext
    . rw [array_size_25, h]
    . intro i h_i _
      rewrite [h] at h_i
      by_cases h: i = 0; simp [h]
      by_cases h: i = 1; simp [h]
      by_cases h: i = 2; simp [h]
      by_cases h: i = 3; simp [h]
      by_cases h: i = 4; simp [h]
      by_cases h: i = 5; simp [h]
      by_cases h: i = 6; simp [h]
      by_cases h: i = 7; simp [h]
      by_cases h: i = 8; simp [h]
      by_cases h: i = 9; simp [h]
      by_cases h: i = 10; simp [h]
      by_cases h: i = 11; simp [h]
      by_cases h: i = 12; simp [h]
      by_cases h: i = 13; simp [h]
      by_cases h: i = 14; simp [h]
      by_cases h: i = 15; simp [h]
      by_cases h: i = 16; simp [h]
      by_cases h: i = 17; simp [h]
      by_cases h: i = 18; simp [h]
      by_cases h: i = 19; simp [h]
      by_cases h: i = 20; simp [h]
      by_cases h: i = 21; simp [h]
      by_cases h: i = 22; simp [h]
      by_cases h: i = 23; simp [h]
      by_cases h: i = 24; simp [h]
      omega


  lemma theta_size (h: state.size = 25):
    (LeanCrypto.HashFunctions.θ state).size = 25
  := by
    unfold LeanCrypto.HashFunctions.θ
    simp [
      h, array_range_25, LeanCrypto.HashFunctions.θ.d,
      array_range_5
    ]

  lemma rho_size (h: state.size = 25):
    (LeanCrypto.HashFunctions.ρ state).size = 25
  := by
    unfold LeanCrypto.HashFunctions.ρ
    simp [h, LeanCrypto.HashFunctions.rotationConstants.eq_def]

  lemma pi_size (h: state.size = 25):
    (LeanCrypto.HashFunctions.π state).size = 25
  := by
    unfold LeanCrypto.HashFunctions.π
    simp [h, LeanCrypto.HashFunctions.piConstants.eq_def, Array.backpermute]

  lemma chi_size (h: state.size = 25):
    (LeanCrypto.HashFunctions.χ state).size = 25
  := by
    unfold LeanCrypto.HashFunctions.χ
    simp [h]

  lemma iota_size (h: state.size = 25):
    (LeanCrypto.HashFunctions.ι round state).size = 25
  := by
    unfold LeanCrypto.HashFunctions.ι
    simp [h]

  lemma keccak_round_size (h: state.size = 25):
    (LeanCrypto.HashFunctions.keccak_round round state).size = 25
  := by
    unfold LeanCrypto.HashFunctions.keccak_round
    simp [Function.comp_apply]
    apply iota_size
    apply chi_size
    apply pi_size
    apply rho_size
    apply theta_size
    exact h

  lemma iota_s_keccak_f_equiv {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_P: 2^200 ≤ P)
    (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24])
    (h_s_0_0: (s c 1 0 0).val = UInt64_to_unpacked_Nat x0)
    (h_s_0_1: (s c 1 0 1).val = UInt64_to_unpacked_Nat x1)
    (h_s_0_2: (s c 1 0 2).val = UInt64_to_unpacked_Nat x2)
    (h_s_0_3: (s c 1 0 3).val = UInt64_to_unpacked_Nat x3)
    (h_s_0_4: (s c 1 0 4).val = UInt64_to_unpacked_Nat x4)
    (h_s_1_0: (s c 1 1 0).val = UInt64_to_unpacked_Nat x5)
    (h_s_1_1: (s c 1 1 1).val = UInt64_to_unpacked_Nat x6)
    (h_s_1_2: (s c 1 1 2).val = UInt64_to_unpacked_Nat x7)
    (h_s_1_3: (s c 1 1 3).val = UInt64_to_unpacked_Nat x8)
    (h_s_1_4: (s c 1 1 4).val = UInt64_to_unpacked_Nat x9)
    (h_s_2_0: (s c 1 2 0).val = UInt64_to_unpacked_Nat x10)
    (h_s_2_1: (s c 1 2 1).val = UInt64_to_unpacked_Nat x11)
    (h_s_2_2: (s c 1 2 2).val = UInt64_to_unpacked_Nat x12)
    (h_s_2_3: (s c 1 2 3).val = UInt64_to_unpacked_Nat x13)
    (h_s_2_4: (s c 1 2 4).val = UInt64_to_unpacked_Nat x14)
    (h_s_3_0: (s c 1 3 0).val = UInt64_to_unpacked_Nat x15)
    (h_s_3_1: (s c 1 3 1).val = UInt64_to_unpacked_Nat x16)
    (h_s_3_2: (s c 1 3 2).val = UInt64_to_unpacked_Nat x17)
    (h_s_3_3: (s c 1 3 3).val = UInt64_to_unpacked_Nat x18)
    (h_s_3_4: (s c 1 3 4).val = UInt64_to_unpacked_Nat x19)
    (h_s_4_0: (s c 1 4 0).val = UInt64_to_unpacked_Nat x20)
    (h_s_4_1: (s c 1 4 1).val = UInt64_to_unpacked_Nat x21)
    (h_s_4_2: (s c 1 4 2).val = UInt64_to_unpacked_Nat x22)
    (h_s_4_3: (s c 1 4 3).val = UInt64_to_unpacked_Nat x23)
    (h_s_4_4: (s c 1 4 4).val = UInt64_to_unpacked_Nat x24)
  :
    .some (iota_s c 24 y x).val =
    (LeanCrypto.HashFunctions.keccakF state)[y.val*5+x.val]?.map UInt64_to_unpacked_Nat
  := by
    have h_keccak_round (round) (state):
      LeanCrypto.HashFunctions.ι round
        (LeanCrypto.HashFunctions.χ
          (LeanCrypto.HashFunctions.π
            (LeanCrypto.HashFunctions.ρ
              (LeanCrypto.HashFunctions.θ state)))) =
      LeanCrypto.HashFunctions.keccak_round round state
    := by
      unfold LeanCrypto.HashFunctions.keccak_round
      simp [Function.comp_apply]
    unfold LeanCrypto.HashFunctions.keccakF
    simp [LeanCrypto.HashFunctions.Rounds.eq_def]
    rewrite [Array.foldl1, ←Array.foldl_toList]
    simp [LeanCrypto.HashFunctions.keccakF.f]
    rewrite [
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
      h_keccak_round, h_keccak_round, h_keccak_round,
    ]
    have h_0 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints (show 0 ∈ Finset.Icc 0 23 by aesop) h_P
      h_state
      h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
      h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
      h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
      h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
      h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    dsimp at h_0
    have h_next_row_1 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨1, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_1
    simp [h_next_row_1] at h_0
    have h_range (x y: Fin 5):y.val*5+x.val < (LeanCrypto.HashFunctions.keccak_round 0 state).size := by
      rewrite [keccak_round_size]
      . omega
      . rewrite [h_state]; rfl
    simp [Array.getElem?_eq_getElem, h_range] at h_0
    have h_state_size: state.size = 25 := by rw [h_state, array_size_25]
    have h_state_size_0:
      (LeanCrypto.HashFunctions.keccak_round 0 state).size = 25
    := by
      rw [keccak_round_size h_state_size]
    have h_mem_1: 1 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_0_0_0 := h_0 0 0
    have h_0_0_1 := h_0 0 1
    have h_0_0_2 := h_0 0 2
    have h_0_0_3 := h_0 0 3
    have h_0_0_4 := h_0 0 4
    have h_0_1_0 := h_0 1 0
    have h_0_1_1 := h_0 1 1
    have h_0_1_2 := h_0 1 2
    have h_0_1_3 := h_0 1 3
    have h_0_1_4 := h_0 1 4
    have h_0_2_0 := h_0 2 0
    have h_0_2_1 := h_0 2 1
    have h_0_2_2 := h_0 2 2
    have h_0_2_3 := h_0 2 3
    have h_0_2_4 := h_0 2 4
    have h_0_3_0 := h_0 3 0
    have h_0_3_1 := h_0 3 1
    have h_0_3_2 := h_0 3 2
    have h_0_3_3 := h_0 3 3
    have h_0_3_4 := h_0 3 4
    have h_0_4_0 := h_0 4 0
    have h_0_4_1 := h_0 4 1
    have h_0_4_2 := h_0 4 2
    have h_0_4_3 := h_0 4 3
    have h_0_4_4 := h_0 4 4
    simp [fin_vals] at h_0_0_0 h_0_0_1 h_0_0_2 h_0_0_3 h_0_0_4 h_0_1_0 h_0_1_1 h_0_1_2 h_0_1_3 h_0_1_4 h_0_2_0 h_0_2_1 h_0_2_2 h_0_2_3 h_0_2_4 h_0_3_0 h_0_3_1 h_0_3_2 h_0_3_3 h_0_3_4 h_0_4_0 h_0_4_1 h_0_4_2 h_0_4_3 h_0_4_4
    have h_1 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_1 h_P
      (array_ext_25 h_state_size_0)
    simp only [Nat.reduceAdd] at h_1
    simp [
      h_0_0_0, h_0_0_1, h_0_0_2, h_0_0_3, h_0_0_4,
      h_0_1_0, h_0_1_1, h_0_1_2, h_0_1_3, h_0_1_4,
      h_0_2_0, h_0_2_1, h_0_2_2, h_0_2_3, h_0_2_4,
      h_0_3_0, h_0_3_1, h_0_3_2, h_0_3_3, h_0_3_4,
      h_0_4_0, h_0_4_1, h_0_4_2, h_0_4_3, h_0_4_4,
    ] at h_1
    clear h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
    clear h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
    clear h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
    clear h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
    clear h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
    clear h_state
    clear h_0_0_0 h_0_0_1 h_0_0_2 h_0_0_3 h_0_0_4
    clear h_0_1_0 h_0_1_1 h_0_1_2 h_0_1_3 h_0_1_4
    clear h_0_2_0 h_0_2_1 h_0_2_2 h_0_2_3 h_0_2_4
    clear h_0_3_0 h_0_3_1 h_0_3_2 h_0_3_3 h_0_3_4
    clear h_0_4_0 h_0_4_1 h_0_4_2 h_0_4_3 h_0_4_4
    clear h_0 h_range
    clear h_keccak_round
    have h_next_row_2 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨2, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_2
    simp [h_next_row_2] at h_1
    have h_range_1 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 1 (LeanCrypto.HashFunctions.keccak_round 0 state)).size
    := by
      rewrite [keccak_round_size]
      . omega
      . rw [keccak_round_size h_state_size]
    simp [Array.getElem?_eq_getElem, h_range_1] at h_1
    have h_state_size_1 := keccak_round_size h_state_size_0 (round := 1)
    have h_mem_2: 2 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_1_0_0 := h_1 0 0
    have h_1_0_1 := h_1 0 1
    have h_1_0_2 := h_1 0 2
    have h_1_0_3 := h_1 0 3
    have h_1_0_4 := h_1 0 4
    have h_1_1_0 := h_1 1 0
    have h_1_1_1 := h_1 1 1
    have h_1_1_2 := h_1 1 2
    have h_1_1_3 := h_1 1 3
    have h_1_1_4 := h_1 1 4
    have h_1_2_0 := h_1 2 0
    have h_1_2_1 := h_1 2 1
    have h_1_2_2 := h_1 2 2
    have h_1_2_3 := h_1 2 3
    have h_1_2_4 := h_1 2 4
    have h_1_3_0 := h_1 3 0
    have h_1_3_1 := h_1 3 1
    have h_1_3_2 := h_1 3 2
    have h_1_3_3 := h_1 3 3
    have h_1_3_4 := h_1 3 4
    have h_1_4_0 := h_1 4 0
    have h_1_4_1 := h_1 4 1
    have h_1_4_2 := h_1 4 2
    have h_1_4_3 := h_1 4 3
    have h_1_4_4 := h_1 4 4
    simp [fin_vals] at h_1_0_0 h_1_0_1 h_1_0_2 h_1_0_3 h_1_0_4 h_1_1_0 h_1_1_1 h_1_1_2 h_1_1_3 h_1_1_4 h_1_2_0 h_1_2_1 h_1_2_2 h_1_2_3 h_1_2_4 h_1_3_0 h_1_3_1 h_1_3_2 h_1_3_3 h_1_3_4 h_1_4_0 h_1_4_1 h_1_4_2 h_1_4_3 h_1_4_4
    have h_2 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_2 h_P
      (array_ext_25 h_state_size_1)
    simp only [Nat.reduceAdd] at h_2
    simp [
      h_1_0_0, h_1_0_1, h_1_0_2, h_1_0_3, h_1_0_4,
      h_1_1_0, h_1_1_1, h_1_1_2, h_1_1_3, h_1_1_4,
      h_1_2_0, h_1_2_1, h_1_2_2, h_1_2_3, h_1_2_4,
      h_1_3_0, h_1_3_1, h_1_3_2, h_1_3_3, h_1_3_4,
      h_1_4_0, h_1_4_1, h_1_4_2, h_1_4_3, h_1_4_4,
    ] at h_2
    clear h_1_0_0 h_1_0_1 h_1_0_2 h_1_0_3 h_1_0_4
    clear h_1_1_0 h_1_1_1 h_1_1_2 h_1_1_3 h_1_1_4
    clear h_1_2_0 h_1_2_1 h_1_2_2 h_1_2_3 h_1_2_4
    clear h_1_3_0 h_1_3_1 h_1_3_2 h_1_3_3 h_1_3_4
    clear h_1_4_0 h_1_4_1 h_1_4_2 h_1_4_3 h_1_4_4
    clear h_1 h_range_1
    have h_next_row_3 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨3, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_3
    simp [h_next_row_3] at h_2
    have h_range_2 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))).size
    := by
      rewrite [keccak_round_size h_state_size_1]
      omega
    simp [Array.getElem?_eq_getElem, h_range_2] at h_2
    have h_state_size_2 := keccak_round_size h_state_size_1 (round := 2)
    have h_mem_3: 3 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_2_0_0 := h_2 0 0
    have h_2_0_1 := h_2 0 1
    have h_2_0_2 := h_2 0 2
    have h_2_0_3 := h_2 0 3
    have h_2_0_4 := h_2 0 4
    have h_2_1_0 := h_2 1 0
    have h_2_1_1 := h_2 1 1
    have h_2_1_2 := h_2 1 2
    have h_2_1_3 := h_2 1 3
    have h_2_1_4 := h_2 1 4
    have h_2_2_0 := h_2 2 0
    have h_2_2_1 := h_2 2 1
    have h_2_2_2 := h_2 2 2
    have h_2_2_3 := h_2 2 3
    have h_2_2_4 := h_2 2 4
    have h_2_3_0 := h_2 3 0
    have h_2_3_1 := h_2 3 1
    have h_2_3_2 := h_2 3 2
    have h_2_3_3 := h_2 3 3
    have h_2_3_4 := h_2 3 4
    have h_2_4_0 := h_2 4 0
    have h_2_4_1 := h_2 4 1
    have h_2_4_2 := h_2 4 2
    have h_2_4_3 := h_2 4 3
    have h_2_4_4 := h_2 4 4
    simp [fin_vals] at h_2_0_0 h_2_0_1 h_2_0_2 h_2_0_3 h_2_0_4 h_2_1_0 h_2_1_1 h_2_1_2 h_2_1_3 h_2_1_4 h_2_2_0 h_2_2_1 h_2_2_2 h_2_2_3 h_2_2_4 h_2_3_0 h_2_3_1 h_2_3_2 h_2_3_3 h_2_3_4 h_2_4_0 h_2_4_1 h_2_4_2 h_2_4_3 h_2_4_4
    have h_3 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_3 h_P
      (array_ext_25 h_state_size_2)
    simp only [Nat.reduceAdd] at h_3
    simp [
      h_2_0_0, h_2_0_1, h_2_0_2, h_2_0_3, h_2_0_4,
      h_2_1_0, h_2_1_1, h_2_1_2, h_2_1_3, h_2_1_4,
      h_2_2_0, h_2_2_1, h_2_2_2, h_2_2_3, h_2_2_4,
      h_2_3_0, h_2_3_1, h_2_3_2, h_2_3_3, h_2_3_4,
      h_2_4_0, h_2_4_1, h_2_4_2, h_2_4_3, h_2_4_4,
    ] at h_3
    clear h_2_0_0 h_2_0_1 h_2_0_2 h_2_0_3 h_2_0_4
    clear h_2_1_0 h_2_1_1 h_2_1_2 h_2_1_3 h_2_1_4
    clear h_2_2_0 h_2_2_1 h_2_2_2 h_2_2_3 h_2_2_4
    clear h_2_3_0 h_2_3_1 h_2_3_2 h_2_3_3 h_2_3_4
    clear h_2_4_0 h_2_4_1 h_2_4_2 h_2_4_3 h_2_4_4
    clear h_2 h_range_2
    have h_next_row_4 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨4, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_4
    simp [h_next_row_4] at h_3
    have h_range_3 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))).size
    := by
      rewrite [keccak_round_size h_state_size_2]
      omega
    simp [Array.getElem?_eq_getElem, h_range_3] at h_3
    have h_state_size_3 := keccak_round_size h_state_size_2 (round := 3)
    have h_mem_4: 4 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_3_0_0 := h_3 0 0
    have h_3_0_1 := h_3 0 1
    have h_3_0_2 := h_3 0 2
    have h_3_0_3 := h_3 0 3
    have h_3_0_4 := h_3 0 4
    have h_3_1_0 := h_3 1 0
    have h_3_1_1 := h_3 1 1
    have h_3_1_2 := h_3 1 2
    have h_3_1_3 := h_3 1 3
    have h_3_1_4 := h_3 1 4
    have h_3_2_0 := h_3 2 0
    have h_3_2_1 := h_3 2 1
    have h_3_2_2 := h_3 2 2
    have h_3_2_3 := h_3 2 3
    have h_3_2_4 := h_3 2 4
    have h_3_3_0 := h_3 3 0
    have h_3_3_1 := h_3 3 1
    have h_3_3_2 := h_3 3 2
    have h_3_3_3 := h_3 3 3
    have h_3_3_4 := h_3 3 4
    have h_3_4_0 := h_3 4 0
    have h_3_4_1 := h_3 4 1
    have h_3_4_2 := h_3 4 2
    have h_3_4_3 := h_3 4 3
    have h_3_4_4 := h_3 4 4
    simp [fin_vals] at h_3_0_0 h_3_0_1 h_3_0_2 h_3_0_3 h_3_0_4 h_3_1_0 h_3_1_1 h_3_1_2 h_3_1_3 h_3_1_4 h_3_2_0 h_3_2_1 h_3_2_2 h_3_2_3 h_3_2_4 h_3_3_0 h_3_3_1 h_3_3_2 h_3_3_3 h_3_3_4 h_3_4_0 h_3_4_1 h_3_4_2 h_3_4_3 h_3_4_4
    have h_4 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_4 h_P
      (array_ext_25 h_state_size_3)
    simp only [Nat.reduceAdd] at h_4
    simp [
      h_3_0_0, h_3_0_1, h_3_0_2, h_3_0_3, h_3_0_4,
      h_3_1_0, h_3_1_1, h_3_1_2, h_3_1_3, h_3_1_4,
      h_3_2_0, h_3_2_1, h_3_2_2, h_3_2_3, h_3_2_4,
      h_3_3_0, h_3_3_1, h_3_3_2, h_3_3_3, h_3_3_4,
      h_3_4_0, h_3_4_1, h_3_4_2, h_3_4_3, h_3_4_4,
    ] at h_4
    clear h_3_0_0 h_3_0_1 h_3_0_2 h_3_0_3 h_3_0_4
    clear h_3_1_0 h_3_1_1 h_3_1_2 h_3_1_3 h_3_1_4
    clear h_3_2_0 h_3_2_1 h_3_2_2 h_3_2_3 h_3_2_4
    clear h_3_3_0 h_3_3_1 h_3_3_2 h_3_3_3 h_3_3_4
    clear h_3_4_0 h_3_4_1 h_3_4_2 h_3_4_3 h_3_4_4
    clear h_3 h_range_3
    have h_next_row_5 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨5, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_5
    simp [h_next_row_5] at h_4
    have h_range_4 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))).size
    := by
      rewrite [keccak_round_size h_state_size_3]
      omega
    simp [Array.getElem?_eq_getElem, h_range_4] at h_4
    have h_state_size_4 := keccak_round_size h_state_size_3 (round := 4)
    have h_mem_5: 5 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_4_0_0 := h_4 0 0
    have h_4_0_1 := h_4 0 1
    have h_4_0_2 := h_4 0 2
    have h_4_0_3 := h_4 0 3
    have h_4_0_4 := h_4 0 4
    have h_4_1_0 := h_4 1 0
    have h_4_1_1 := h_4 1 1
    have h_4_1_2 := h_4 1 2
    have h_4_1_3 := h_4 1 3
    have h_4_1_4 := h_4 1 4
    have h_4_2_0 := h_4 2 0
    have h_4_2_1 := h_4 2 1
    have h_4_2_2 := h_4 2 2
    have h_4_2_3 := h_4 2 3
    have h_4_2_4 := h_4 2 4
    have h_4_3_0 := h_4 3 0
    have h_4_3_1 := h_4 3 1
    have h_4_3_2 := h_4 3 2
    have h_4_3_3 := h_4 3 3
    have h_4_3_4 := h_4 3 4
    have h_4_4_0 := h_4 4 0
    have h_4_4_1 := h_4 4 1
    have h_4_4_2 := h_4 4 2
    have h_4_4_3 := h_4 4 3
    have h_4_4_4 := h_4 4 4
    simp [fin_vals] at h_4_0_0 h_4_0_1 h_4_0_2 h_4_0_3 h_4_0_4 h_4_1_0 h_4_1_1 h_4_1_2 h_4_1_3 h_4_1_4 h_4_2_0 h_4_2_1 h_4_2_2 h_4_2_3 h_4_2_4 h_4_3_0 h_4_3_1 h_4_3_2 h_4_3_3 h_4_3_4 h_4_4_0 h_4_4_1 h_4_4_2 h_4_4_3 h_4_4_4
    have h_5 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_5 h_P
      (array_ext_25 h_state_size_4)
    simp only [Nat.reduceAdd] at h_5
    simp [
      h_4_0_0, h_4_0_1, h_4_0_2, h_4_0_3, h_4_0_4,
      h_4_1_0, h_4_1_1, h_4_1_2, h_4_1_3, h_4_1_4,
      h_4_2_0, h_4_2_1, h_4_2_2, h_4_2_3, h_4_2_4,
      h_4_3_0, h_4_3_1, h_4_3_2, h_4_3_3, h_4_3_4,
      h_4_4_0, h_4_4_1, h_4_4_2, h_4_4_3, h_4_4_4,
    ] at h_5
    clear h_4_0_0 h_4_0_1 h_4_0_2 h_4_0_3 h_4_0_4
    clear h_4_1_0 h_4_1_1 h_4_1_2 h_4_1_3 h_4_1_4
    clear h_4_2_0 h_4_2_1 h_4_2_2 h_4_2_3 h_4_2_4
    clear h_4_3_0 h_4_3_1 h_4_3_2 h_4_3_3 h_4_3_4
    clear h_4_4_0 h_4_4_1 h_4_4_2 h_4_4_3 h_4_4_4
    clear h_4 h_range_4
    have h_next_row_6 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨6, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_6
    simp [h_next_row_6] at h_5
    have h_range_5 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))).size
    := by
      rewrite [keccak_round_size h_state_size_4]
      omega
    simp [Array.getElem?_eq_getElem, h_range_5] at h_5
    have h_state_size_5 := keccak_round_size h_state_size_4 (round := 5)
    have h_mem_6: 6 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_5_0_0 := h_5 0 0
    have h_5_0_1 := h_5 0 1
    have h_5_0_2 := h_5 0 2
    have h_5_0_3 := h_5 0 3
    have h_5_0_4 := h_5 0 4
    have h_5_1_0 := h_5 1 0
    have h_5_1_1 := h_5 1 1
    have h_5_1_2 := h_5 1 2
    have h_5_1_3 := h_5 1 3
    have h_5_1_4 := h_5 1 4
    have h_5_2_0 := h_5 2 0
    have h_5_2_1 := h_5 2 1
    have h_5_2_2 := h_5 2 2
    have h_5_2_3 := h_5 2 3
    have h_5_2_4 := h_5 2 4
    have h_5_3_0 := h_5 3 0
    have h_5_3_1 := h_5 3 1
    have h_5_3_2 := h_5 3 2
    have h_5_3_3 := h_5 3 3
    have h_5_3_4 := h_5 3 4
    have h_5_4_0 := h_5 4 0
    have h_5_4_1 := h_5 4 1
    have h_5_4_2 := h_5 4 2
    have h_5_4_3 := h_5 4 3
    have h_5_4_4 := h_5 4 4
    simp [fin_vals] at h_5_0_0 h_5_0_1 h_5_0_2 h_5_0_3 h_5_0_4 h_5_1_0 h_5_1_1 h_5_1_2 h_5_1_3 h_5_1_4 h_5_2_0 h_5_2_1 h_5_2_2 h_5_2_3 h_5_2_4 h_5_3_0 h_5_3_1 h_5_3_2 h_5_3_3 h_5_3_4 h_5_4_0 h_5_4_1 h_5_4_2 h_5_4_3 h_5_4_4
    have h_6 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_6 h_P
      (array_ext_25 h_state_size_5)
    simp only [Nat.reduceAdd] at h_6
    simp [
      h_5_0_0, h_5_0_1, h_5_0_2, h_5_0_3, h_5_0_4,
      h_5_1_0, h_5_1_1, h_5_1_2, h_5_1_3, h_5_1_4,
      h_5_2_0, h_5_2_1, h_5_2_2, h_5_2_3, h_5_2_4,
      h_5_3_0, h_5_3_1, h_5_3_2, h_5_3_3, h_5_3_4,
      h_5_4_0, h_5_4_1, h_5_4_2, h_5_4_3, h_5_4_4,
    ] at h_6
    clear h_5_0_0 h_5_0_1 h_5_0_2 h_5_0_3 h_5_0_4
    clear h_5_1_0 h_5_1_1 h_5_1_2 h_5_1_3 h_5_1_4
    clear h_5_2_0 h_5_2_1 h_5_2_2 h_5_2_3 h_5_2_4
    clear h_5_3_0 h_5_3_1 h_5_3_2 h_5_3_3 h_5_3_4
    clear h_5_4_0 h_5_4_1 h_5_4_2 h_5_4_3 h_5_4_4
    clear h_5 h_range_5
    have h_next_row_7 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨7, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_7
    simp [h_next_row_7] at h_6
    have h_range_6 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))).size
    := by
      rewrite [keccak_round_size h_state_size_5]
      omega
    simp [Array.getElem?_eq_getElem, h_range_6] at h_6
    have h_state_size_6 := keccak_round_size h_state_size_5 (round := 6)
    have h_mem_7: 7 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_6_0_0 := h_6 0 0
    have h_6_0_1 := h_6 0 1
    have h_6_0_2 := h_6 0 2
    have h_6_0_3 := h_6 0 3
    have h_6_0_4 := h_6 0 4
    have h_6_1_0 := h_6 1 0
    have h_6_1_1 := h_6 1 1
    have h_6_1_2 := h_6 1 2
    have h_6_1_3 := h_6 1 3
    have h_6_1_4 := h_6 1 4
    have h_6_2_0 := h_6 2 0
    have h_6_2_1 := h_6 2 1
    have h_6_2_2 := h_6 2 2
    have h_6_2_3 := h_6 2 3
    have h_6_2_4 := h_6 2 4
    have h_6_3_0 := h_6 3 0
    have h_6_3_1 := h_6 3 1
    have h_6_3_2 := h_6 3 2
    have h_6_3_3 := h_6 3 3
    have h_6_3_4 := h_6 3 4
    have h_6_4_0 := h_6 4 0
    have h_6_4_1 := h_6 4 1
    have h_6_4_2 := h_6 4 2
    have h_6_4_3 := h_6 4 3
    have h_6_4_4 := h_6 4 4
    simp [fin_vals] at h_6_0_0 h_6_0_1 h_6_0_2 h_6_0_3 h_6_0_4 h_6_1_0 h_6_1_1 h_6_1_2 h_6_1_3 h_6_1_4 h_6_2_0 h_6_2_1 h_6_2_2 h_6_2_3 h_6_2_4 h_6_3_0 h_6_3_1 h_6_3_2 h_6_3_3 h_6_3_4 h_6_4_0 h_6_4_1 h_6_4_2 h_6_4_3 h_6_4_4
    have h_7 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_7 h_P
      (array_ext_25 h_state_size_6)
    simp only [Nat.reduceAdd] at h_7
    simp [
      h_6_0_0, h_6_0_1, h_6_0_2, h_6_0_3, h_6_0_4,
      h_6_1_0, h_6_1_1, h_6_1_2, h_6_1_3, h_6_1_4,
      h_6_2_0, h_6_2_1, h_6_2_2, h_6_2_3, h_6_2_4,
      h_6_3_0, h_6_3_1, h_6_3_2, h_6_3_3, h_6_3_4,
      h_6_4_0, h_6_4_1, h_6_4_2, h_6_4_3, h_6_4_4,
    ] at h_7
    clear h_6_0_0 h_6_0_1 h_6_0_2 h_6_0_3 h_6_0_4
    clear h_6_1_0 h_6_1_1 h_6_1_2 h_6_1_3 h_6_1_4
    clear h_6_2_0 h_6_2_1 h_6_2_2 h_6_2_3 h_6_2_4
    clear h_6_3_0 h_6_3_1 h_6_3_2 h_6_3_3 h_6_3_4
    clear h_6_4_0 h_6_4_1 h_6_4_2 h_6_4_3 h_6_4_4
    clear h_6 h_range_6
    have h_next_row_8 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨8, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_8
    simp [h_next_row_8] at h_7
    have h_range_7 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))).size
    := by
      rewrite [keccak_round_size h_state_size_6]
      omega
    simp [Array.getElem?_eq_getElem, h_range_7] at h_7
    have h_state_size_7 := keccak_round_size h_state_size_6 (round := 7)
    have h_mem_8: 8 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_7_0_0 := h_7 0 0
    have h_7_0_1 := h_7 0 1
    have h_7_0_2 := h_7 0 2
    have h_7_0_3 := h_7 0 3
    have h_7_0_4 := h_7 0 4
    have h_7_1_0 := h_7 1 0
    have h_7_1_1 := h_7 1 1
    have h_7_1_2 := h_7 1 2
    have h_7_1_3 := h_7 1 3
    have h_7_1_4 := h_7 1 4
    have h_7_2_0 := h_7 2 0
    have h_7_2_1 := h_7 2 1
    have h_7_2_2 := h_7 2 2
    have h_7_2_3 := h_7 2 3
    have h_7_2_4 := h_7 2 4
    have h_7_3_0 := h_7 3 0
    have h_7_3_1 := h_7 3 1
    have h_7_3_2 := h_7 3 2
    have h_7_3_3 := h_7 3 3
    have h_7_3_4 := h_7 3 4
    have h_7_4_0 := h_7 4 0
    have h_7_4_1 := h_7 4 1
    have h_7_4_2 := h_7 4 2
    have h_7_4_3 := h_7 4 3
    have h_7_4_4 := h_7 4 4
    simp [fin_vals] at h_7_0_0 h_7_0_1 h_7_0_2 h_7_0_3 h_7_0_4 h_7_1_0 h_7_1_1 h_7_1_2 h_7_1_3 h_7_1_4 h_7_2_0 h_7_2_1 h_7_2_2 h_7_2_3 h_7_2_4 h_7_3_0 h_7_3_1 h_7_3_2 h_7_3_3 h_7_3_4 h_7_4_0 h_7_4_1 h_7_4_2 h_7_4_3 h_7_4_4
    have h_8 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_8 h_P
      (array_ext_25 h_state_size_7)
    simp only [Nat.reduceAdd] at h_8
    simp [
      h_7_0_0, h_7_0_1, h_7_0_2, h_7_0_3, h_7_0_4,
      h_7_1_0, h_7_1_1, h_7_1_2, h_7_1_3, h_7_1_4,
      h_7_2_0, h_7_2_1, h_7_2_2, h_7_2_3, h_7_2_4,
      h_7_3_0, h_7_3_1, h_7_3_2, h_7_3_3, h_7_3_4,
      h_7_4_0, h_7_4_1, h_7_4_2, h_7_4_3, h_7_4_4,
    ] at h_8
    clear h_7_0_0 h_7_0_1 h_7_0_2 h_7_0_3 h_7_0_4
    clear h_7_1_0 h_7_1_1 h_7_1_2 h_7_1_3 h_7_1_4
    clear h_7_2_0 h_7_2_1 h_7_2_2 h_7_2_3 h_7_2_4
    clear h_7_3_0 h_7_3_1 h_7_3_2 h_7_3_3 h_7_3_4
    clear h_7_4_0 h_7_4_1 h_7_4_2 h_7_4_3 h_7_4_4
    clear h_7 h_range_7
    have h_next_row_9 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨9, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_9
    simp [h_next_row_9] at h_8
    have h_range_8 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_7]
      omega
    simp [Array.getElem?_eq_getElem, h_range_8] at h_8
    have h_state_size_8 := keccak_round_size h_state_size_7 (round := 8)
    have h_mem_9: 9 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_8_0_0 := h_8 0 0
    have h_8_0_1 := h_8 0 1
    have h_8_0_2 := h_8 0 2
    have h_8_0_3 := h_8 0 3
    have h_8_0_4 := h_8 0 4
    have h_8_1_0 := h_8 1 0
    have h_8_1_1 := h_8 1 1
    have h_8_1_2 := h_8 1 2
    have h_8_1_3 := h_8 1 3
    have h_8_1_4 := h_8 1 4
    have h_8_2_0 := h_8 2 0
    have h_8_2_1 := h_8 2 1
    have h_8_2_2 := h_8 2 2
    have h_8_2_3 := h_8 2 3
    have h_8_2_4 := h_8 2 4
    have h_8_3_0 := h_8 3 0
    have h_8_3_1 := h_8 3 1
    have h_8_3_2 := h_8 3 2
    have h_8_3_3 := h_8 3 3
    have h_8_3_4 := h_8 3 4
    have h_8_4_0 := h_8 4 0
    have h_8_4_1 := h_8 4 1
    have h_8_4_2 := h_8 4 2
    have h_8_4_3 := h_8 4 3
    have h_8_4_4 := h_8 4 4
    simp [fin_vals] at h_8_0_0 h_8_0_1 h_8_0_2 h_8_0_3 h_8_0_4 h_8_1_0 h_8_1_1 h_8_1_2 h_8_1_3 h_8_1_4 h_8_2_0 h_8_2_1 h_8_2_2 h_8_2_3 h_8_2_4 h_8_3_0 h_8_3_1 h_8_3_2 h_8_3_3 h_8_3_4 h_8_4_0 h_8_4_1 h_8_4_2 h_8_4_3 h_8_4_4
    have h_9 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_9 h_P
      (array_ext_25 h_state_size_8)
    simp only [Nat.reduceAdd] at h_9
    simp [
      h_8_0_0, h_8_0_1, h_8_0_2, h_8_0_3, h_8_0_4,
      h_8_1_0, h_8_1_1, h_8_1_2, h_8_1_3, h_8_1_4,
      h_8_2_0, h_8_2_1, h_8_2_2, h_8_2_3, h_8_2_4,
      h_8_3_0, h_8_3_1, h_8_3_2, h_8_3_3, h_8_3_4,
      h_8_4_0, h_8_4_1, h_8_4_2, h_8_4_3, h_8_4_4,
    ] at h_9
    clear h_8_0_0 h_8_0_1 h_8_0_2 h_8_0_3 h_8_0_4
    clear h_8_1_0 h_8_1_1 h_8_1_2 h_8_1_3 h_8_1_4
    clear h_8_2_0 h_8_2_1 h_8_2_2 h_8_2_3 h_8_2_4
    clear h_8_3_0 h_8_3_1 h_8_3_2 h_8_3_3 h_8_3_4
    clear h_8_4_0 h_8_4_1 h_8_4_2 h_8_4_3 h_8_4_4
    clear h_8 h_range_8
    have h_next_row_10 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨10, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_10
    simp [h_next_row_10] at h_9
    have h_range_9 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_8]
      omega
    simp [Array.getElem?_eq_getElem, h_range_9] at h_9
    have h_state_size_9 := keccak_round_size h_state_size_8 (round := 9)
    have h_mem_10: 10 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_9_0_0 := h_9 0 0
    have h_9_0_1 := h_9 0 1
    have h_9_0_2 := h_9 0 2
    have h_9_0_3 := h_9 0 3
    have h_9_0_4 := h_9 0 4
    have h_9_1_0 := h_9 1 0
    have h_9_1_1 := h_9 1 1
    have h_9_1_2 := h_9 1 2
    have h_9_1_3 := h_9 1 3
    have h_9_1_4 := h_9 1 4
    have h_9_2_0 := h_9 2 0
    have h_9_2_1 := h_9 2 1
    have h_9_2_2 := h_9 2 2
    have h_9_2_3 := h_9 2 3
    have h_9_2_4 := h_9 2 4
    have h_9_3_0 := h_9 3 0
    have h_9_3_1 := h_9 3 1
    have h_9_3_2 := h_9 3 2
    have h_9_3_3 := h_9 3 3
    have h_9_3_4 := h_9 3 4
    have h_9_4_0 := h_9 4 0
    have h_9_4_1 := h_9 4 1
    have h_9_4_2 := h_9 4 2
    have h_9_4_3 := h_9 4 3
    have h_9_4_4 := h_9 4 4
    simp [fin_vals] at h_9_0_0 h_9_0_1 h_9_0_2 h_9_0_3 h_9_0_4 h_9_1_0 h_9_1_1 h_9_1_2 h_9_1_3 h_9_1_4 h_9_2_0 h_9_2_1 h_9_2_2 h_9_2_3 h_9_2_4 h_9_3_0 h_9_3_1 h_9_3_2 h_9_3_3 h_9_3_4 h_9_4_0 h_9_4_1 h_9_4_2 h_9_4_3 h_9_4_4
    have h_10 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_10 h_P
      (array_ext_25 h_state_size_9)
    simp only [Nat.reduceAdd] at h_10
    simp [
      h_9_0_0, h_9_0_1, h_9_0_2, h_9_0_3, h_9_0_4,
      h_9_1_0, h_9_1_1, h_9_1_2, h_9_1_3, h_9_1_4,
      h_9_2_0, h_9_2_1, h_9_2_2, h_9_2_3, h_9_2_4,
      h_9_3_0, h_9_3_1, h_9_3_2, h_9_3_3, h_9_3_4,
      h_9_4_0, h_9_4_1, h_9_4_2, h_9_4_3, h_9_4_4,
    ] at h_10
    clear h_9_0_0 h_9_0_1 h_9_0_2 h_9_0_3 h_9_0_4
    clear h_9_1_0 h_9_1_1 h_9_1_2 h_9_1_3 h_9_1_4
    clear h_9_2_0 h_9_2_1 h_9_2_2 h_9_2_3 h_9_2_4
    clear h_9_3_0 h_9_3_1 h_9_3_2 h_9_3_3 h_9_3_4
    clear h_9_4_0 h_9_4_1 h_9_4_2 h_9_4_3 h_9_4_4
    clear h_9 h_range_9
    have h_next_row_11 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨11, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_11
    simp [h_next_row_11] at h_10
    have h_range_10 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_9]
      omega
    simp [Array.getElem?_eq_getElem, h_range_10] at h_10
    have h_state_size_10 := keccak_round_size h_state_size_9 (round := 10)
    have h_mem_11: 11 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_10_0_0 := h_10 0 0
    have h_10_0_1 := h_10 0 1
    have h_10_0_2 := h_10 0 2
    have h_10_0_3 := h_10 0 3
    have h_10_0_4 := h_10 0 4
    have h_10_1_0 := h_10 1 0
    have h_10_1_1 := h_10 1 1
    have h_10_1_2 := h_10 1 2
    have h_10_1_3 := h_10 1 3
    have h_10_1_4 := h_10 1 4
    have h_10_2_0 := h_10 2 0
    have h_10_2_1 := h_10 2 1
    have h_10_2_2 := h_10 2 2
    have h_10_2_3 := h_10 2 3
    have h_10_2_4 := h_10 2 4
    have h_10_3_0 := h_10 3 0
    have h_10_3_1 := h_10 3 1
    have h_10_3_2 := h_10 3 2
    have h_10_3_3 := h_10 3 3
    have h_10_3_4 := h_10 3 4
    have h_10_4_0 := h_10 4 0
    have h_10_4_1 := h_10 4 1
    have h_10_4_2 := h_10 4 2
    have h_10_4_3 := h_10 4 3
    have h_10_4_4 := h_10 4 4
    simp [fin_vals] at h_10_0_0 h_10_0_1 h_10_0_2 h_10_0_3 h_10_0_4 h_10_1_0 h_10_1_1 h_10_1_2 h_10_1_3 h_10_1_4 h_10_2_0 h_10_2_1 h_10_2_2 h_10_2_3 h_10_2_4 h_10_3_0 h_10_3_1 h_10_3_2 h_10_3_3 h_10_3_4 h_10_4_0 h_10_4_1 h_10_4_2 h_10_4_3 h_10_4_4
    have h_11 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_11 h_P
      (array_ext_25 h_state_size_10)
    simp only [Nat.reduceAdd] at h_11
    simp [
      h_10_0_0, h_10_0_1, h_10_0_2, h_10_0_3, h_10_0_4,
      h_10_1_0, h_10_1_1, h_10_1_2, h_10_1_3, h_10_1_4,
      h_10_2_0, h_10_2_1, h_10_2_2, h_10_2_3, h_10_2_4,
      h_10_3_0, h_10_3_1, h_10_3_2, h_10_3_3, h_10_3_4,
      h_10_4_0, h_10_4_1, h_10_4_2, h_10_4_3, h_10_4_4,
    ] at h_11
    clear h_10_0_0 h_10_0_1 h_10_0_2 h_10_0_3 h_10_0_4
    clear h_10_1_0 h_10_1_1 h_10_1_2 h_10_1_3 h_10_1_4
    clear h_10_2_0 h_10_2_1 h_10_2_2 h_10_2_3 h_10_2_4
    clear h_10_3_0 h_10_3_1 h_10_3_2 h_10_3_3 h_10_3_4
    clear h_10_4_0 h_10_4_1 h_10_4_2 h_10_4_3 h_10_4_4
    clear h_10 h_range_10
    have h_next_row_12 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨12, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_12
    simp [h_next_row_12] at h_11
    have h_range_11 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_10]
      omega
    simp [Array.getElem?_eq_getElem, h_range_11] at h_11
    have h_state_size_11 := keccak_round_size h_state_size_10 (round := 11)
    have h_mem_12: 12 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_11_0_0 := h_11 0 0
    have h_11_0_1 := h_11 0 1
    have h_11_0_2 := h_11 0 2
    have h_11_0_3 := h_11 0 3
    have h_11_0_4 := h_11 0 4
    have h_11_1_0 := h_11 1 0
    have h_11_1_1 := h_11 1 1
    have h_11_1_2 := h_11 1 2
    have h_11_1_3 := h_11 1 3
    have h_11_1_4 := h_11 1 4
    have h_11_2_0 := h_11 2 0
    have h_11_2_1 := h_11 2 1
    have h_11_2_2 := h_11 2 2
    have h_11_2_3 := h_11 2 3
    have h_11_2_4 := h_11 2 4
    have h_11_3_0 := h_11 3 0
    have h_11_3_1 := h_11 3 1
    have h_11_3_2 := h_11 3 2
    have h_11_3_3 := h_11 3 3
    have h_11_3_4 := h_11 3 4
    have h_11_4_0 := h_11 4 0
    have h_11_4_1 := h_11 4 1
    have h_11_4_2 := h_11 4 2
    have h_11_4_3 := h_11 4 3
    have h_11_4_4 := h_11 4 4
    simp [fin_vals] at h_11_0_0 h_11_0_1 h_11_0_2 h_11_0_3 h_11_0_4 h_11_1_0 h_11_1_1 h_11_1_2 h_11_1_3 h_11_1_4 h_11_2_0 h_11_2_1 h_11_2_2 h_11_2_3 h_11_2_4 h_11_3_0 h_11_3_1 h_11_3_2 h_11_3_3 h_11_3_4 h_11_4_0 h_11_4_1 h_11_4_2 h_11_4_3 h_11_4_4
    have h_12 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_12 h_P
      (array_ext_25 h_state_size_11)
    simp only [Nat.reduceAdd] at h_12
    simp [
      h_11_0_0, h_11_0_1, h_11_0_2, h_11_0_3, h_11_0_4,
      h_11_1_0, h_11_1_1, h_11_1_2, h_11_1_3, h_11_1_4,
      h_11_2_0, h_11_2_1, h_11_2_2, h_11_2_3, h_11_2_4,
      h_11_3_0, h_11_3_1, h_11_3_2, h_11_3_3, h_11_3_4,
      h_11_4_0, h_11_4_1, h_11_4_2, h_11_4_3, h_11_4_4,
    ] at h_12
    clear h_11_0_0 h_11_0_1 h_11_0_2 h_11_0_3 h_11_0_4
    clear h_11_1_0 h_11_1_1 h_11_1_2 h_11_1_3 h_11_1_4
    clear h_11_2_0 h_11_2_1 h_11_2_2 h_11_2_3 h_11_2_4
    clear h_11_3_0 h_11_3_1 h_11_3_2 h_11_3_3 h_11_3_4
    clear h_11_4_0 h_11_4_1 h_11_4_2 h_11_4_3 h_11_4_4
    clear h_11 h_range_11
    have h_next_row_13 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨13, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_13
    simp [h_next_row_13] at h_12
    have h_range_12 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_11]
      omega
    simp [Array.getElem?_eq_getElem, h_range_12] at h_12
    have h_state_size_12 := keccak_round_size h_state_size_11 (round := 12)
    have h_mem_13: 13 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_12_0_0 := h_12 0 0
    have h_12_0_1 := h_12 0 1
    have h_12_0_2 := h_12 0 2
    have h_12_0_3 := h_12 0 3
    have h_12_0_4 := h_12 0 4
    have h_12_1_0 := h_12 1 0
    have h_12_1_1 := h_12 1 1
    have h_12_1_2 := h_12 1 2
    have h_12_1_3 := h_12 1 3
    have h_12_1_4 := h_12 1 4
    have h_12_2_0 := h_12 2 0
    have h_12_2_1 := h_12 2 1
    have h_12_2_2 := h_12 2 2
    have h_12_2_3 := h_12 2 3
    have h_12_2_4 := h_12 2 4
    have h_12_3_0 := h_12 3 0
    have h_12_3_1 := h_12 3 1
    have h_12_3_2 := h_12 3 2
    have h_12_3_3 := h_12 3 3
    have h_12_3_4 := h_12 3 4
    have h_12_4_0 := h_12 4 0
    have h_12_4_1 := h_12 4 1
    have h_12_4_2 := h_12 4 2
    have h_12_4_3 := h_12 4 3
    have h_12_4_4 := h_12 4 4
    simp [fin_vals] at h_12_0_0 h_12_0_1 h_12_0_2 h_12_0_3 h_12_0_4 h_12_1_0 h_12_1_1 h_12_1_2 h_12_1_3 h_12_1_4 h_12_2_0 h_12_2_1 h_12_2_2 h_12_2_3 h_12_2_4 h_12_3_0 h_12_3_1 h_12_3_2 h_12_3_3 h_12_3_4 h_12_4_0 h_12_4_1 h_12_4_2 h_12_4_3 h_12_4_4
    have h_13 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_13 h_P
      (array_ext_25 h_state_size_12)
    simp only [Nat.reduceAdd] at h_13
    simp [
      h_12_0_0, h_12_0_1, h_12_0_2, h_12_0_3, h_12_0_4,
      h_12_1_0, h_12_1_1, h_12_1_2, h_12_1_3, h_12_1_4,
      h_12_2_0, h_12_2_1, h_12_2_2, h_12_2_3, h_12_2_4,
      h_12_3_0, h_12_3_1, h_12_3_2, h_12_3_3, h_12_3_4,
      h_12_4_0, h_12_4_1, h_12_4_2, h_12_4_3, h_12_4_4,
    ] at h_13
    clear h_12_0_0 h_12_0_1 h_12_0_2 h_12_0_3 h_12_0_4
    clear h_12_1_0 h_12_1_1 h_12_1_2 h_12_1_3 h_12_1_4
    clear h_12_2_0 h_12_2_1 h_12_2_2 h_12_2_3 h_12_2_4
    clear h_12_3_0 h_12_3_1 h_12_3_2 h_12_3_3 h_12_3_4
    clear h_12_4_0 h_12_4_1 h_12_4_2 h_12_4_3 h_12_4_4
    clear h_12 h_range_12
    have h_next_row_14 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨14, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_14
    simp [h_next_row_14] at h_13
    have h_range_13 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_12]
      omega
    simp [Array.getElem?_eq_getElem, h_range_13] at h_13
    have h_state_size_13 := keccak_round_size h_state_size_12 (round := 13)
    have h_mem_14: 14 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_13_0_0 := h_13 0 0
    have h_13_0_1 := h_13 0 1
    have h_13_0_2 := h_13 0 2
    have h_13_0_3 := h_13 0 3
    have h_13_0_4 := h_13 0 4
    have h_13_1_0 := h_13 1 0
    have h_13_1_1 := h_13 1 1
    have h_13_1_2 := h_13 1 2
    have h_13_1_3 := h_13 1 3
    have h_13_1_4 := h_13 1 4
    have h_13_2_0 := h_13 2 0
    have h_13_2_1 := h_13 2 1
    have h_13_2_2 := h_13 2 2
    have h_13_2_3 := h_13 2 3
    have h_13_2_4 := h_13 2 4
    have h_13_3_0 := h_13 3 0
    have h_13_3_1 := h_13 3 1
    have h_13_3_2 := h_13 3 2
    have h_13_3_3 := h_13 3 3
    have h_13_3_4 := h_13 3 4
    have h_13_4_0 := h_13 4 0
    have h_13_4_1 := h_13 4 1
    have h_13_4_2 := h_13 4 2
    have h_13_4_3 := h_13 4 3
    have h_13_4_4 := h_13 4 4
    simp [fin_vals] at h_13_0_0 h_13_0_1 h_13_0_2 h_13_0_3 h_13_0_4 h_13_1_0 h_13_1_1 h_13_1_2 h_13_1_3 h_13_1_4 h_13_2_0 h_13_2_1 h_13_2_2 h_13_2_3 h_13_2_4 h_13_3_0 h_13_3_1 h_13_3_2 h_13_3_3 h_13_3_4 h_13_4_0 h_13_4_1 h_13_4_2 h_13_4_3 h_13_4_4
    have h_14 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_14 h_P
      (array_ext_25 h_state_size_13)
    simp only [Nat.reduceAdd] at h_14
    simp [
      h_13_0_0, h_13_0_1, h_13_0_2, h_13_0_3, h_13_0_4,
      h_13_1_0, h_13_1_1, h_13_1_2, h_13_1_3, h_13_1_4,
      h_13_2_0, h_13_2_1, h_13_2_2, h_13_2_3, h_13_2_4,
      h_13_3_0, h_13_3_1, h_13_3_2, h_13_3_3, h_13_3_4,
      h_13_4_0, h_13_4_1, h_13_4_2, h_13_4_3, h_13_4_4,
    ] at h_14
    clear h_13_0_0 h_13_0_1 h_13_0_2 h_13_0_3 h_13_0_4
    clear h_13_1_0 h_13_1_1 h_13_1_2 h_13_1_3 h_13_1_4
    clear h_13_2_0 h_13_2_1 h_13_2_2 h_13_2_3 h_13_2_4
    clear h_13_3_0 h_13_3_1 h_13_3_2 h_13_3_3 h_13_3_4
    clear h_13_4_0 h_13_4_1 h_13_4_2 h_13_4_3 h_13_4_4
    clear h_13 h_range_13
    have h_next_row_15 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨15, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_15
    simp [h_next_row_15] at h_14
    have h_range_14 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_13]
      omega
    simp [Array.getElem?_eq_getElem, h_range_14] at h_14
    have h_state_size_14 := keccak_round_size h_state_size_13 (round := 14)
    have h_mem_15: 15 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_14_0_0 := h_14 0 0
    have h_14_0_1 := h_14 0 1
    have h_14_0_2 := h_14 0 2
    have h_14_0_3 := h_14 0 3
    have h_14_0_4 := h_14 0 4
    have h_14_1_0 := h_14 1 0
    have h_14_1_1 := h_14 1 1
    have h_14_1_2 := h_14 1 2
    have h_14_1_3 := h_14 1 3
    have h_14_1_4 := h_14 1 4
    have h_14_2_0 := h_14 2 0
    have h_14_2_1 := h_14 2 1
    have h_14_2_2 := h_14 2 2
    have h_14_2_3 := h_14 2 3
    have h_14_2_4 := h_14 2 4
    have h_14_3_0 := h_14 3 0
    have h_14_3_1 := h_14 3 1
    have h_14_3_2 := h_14 3 2
    have h_14_3_3 := h_14 3 3
    have h_14_3_4 := h_14 3 4
    have h_14_4_0 := h_14 4 0
    have h_14_4_1 := h_14 4 1
    have h_14_4_2 := h_14 4 2
    have h_14_4_3 := h_14 4 3
    have h_14_4_4 := h_14 4 4
    simp [fin_vals] at h_14_0_0 h_14_0_1 h_14_0_2 h_14_0_3 h_14_0_4 h_14_1_0 h_14_1_1 h_14_1_2 h_14_1_3 h_14_1_4 h_14_2_0 h_14_2_1 h_14_2_2 h_14_2_3 h_14_2_4 h_14_3_0 h_14_3_1 h_14_3_2 h_14_3_3 h_14_3_4 h_14_4_0 h_14_4_1 h_14_4_2 h_14_4_3 h_14_4_4
    have h_15 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_15 h_P
      (array_ext_25 h_state_size_14)
    simp only [Nat.reduceAdd] at h_15
    simp [
      h_14_0_0, h_14_0_1, h_14_0_2, h_14_0_3, h_14_0_4,
      h_14_1_0, h_14_1_1, h_14_1_2, h_14_1_3, h_14_1_4,
      h_14_2_0, h_14_2_1, h_14_2_2, h_14_2_3, h_14_2_4,
      h_14_3_0, h_14_3_1, h_14_3_2, h_14_3_3, h_14_3_4,
      h_14_4_0, h_14_4_1, h_14_4_2, h_14_4_3, h_14_4_4,
    ] at h_15
    clear h_14_0_0 h_14_0_1 h_14_0_2 h_14_0_3 h_14_0_4
    clear h_14_1_0 h_14_1_1 h_14_1_2 h_14_1_3 h_14_1_4
    clear h_14_2_0 h_14_2_1 h_14_2_2 h_14_2_3 h_14_2_4
    clear h_14_3_0 h_14_3_1 h_14_3_2 h_14_3_3 h_14_3_4
    clear h_14_4_0 h_14_4_1 h_14_4_2 h_14_4_3 h_14_4_4
    clear h_14 h_range_14
    have h_next_row_16 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨16, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_16
    simp [h_next_row_16] at h_15
    have h_range_15 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_14]
      omega
    simp [Array.getElem?_eq_getElem, h_range_15] at h_15
    have h_state_size_15 := keccak_round_size h_state_size_14 (round := 15)
    have h_mem_16: 16 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_15_0_0 := h_15 0 0
    have h_15_0_1 := h_15 0 1
    have h_15_0_2 := h_15 0 2
    have h_15_0_3 := h_15 0 3
    have h_15_0_4 := h_15 0 4
    have h_15_1_0 := h_15 1 0
    have h_15_1_1 := h_15 1 1
    have h_15_1_2 := h_15 1 2
    have h_15_1_3 := h_15 1 3
    have h_15_1_4 := h_15 1 4
    have h_15_2_0 := h_15 2 0
    have h_15_2_1 := h_15 2 1
    have h_15_2_2 := h_15 2 2
    have h_15_2_3 := h_15 2 3
    have h_15_2_4 := h_15 2 4
    have h_15_3_0 := h_15 3 0
    have h_15_3_1 := h_15 3 1
    have h_15_3_2 := h_15 3 2
    have h_15_3_3 := h_15 3 3
    have h_15_3_4 := h_15 3 4
    have h_15_4_0 := h_15 4 0
    have h_15_4_1 := h_15 4 1
    have h_15_4_2 := h_15 4 2
    have h_15_4_3 := h_15 4 3
    have h_15_4_4 := h_15 4 4
    simp [fin_vals] at h_15_0_0 h_15_0_1 h_15_0_2 h_15_0_3 h_15_0_4 h_15_1_0 h_15_1_1 h_15_1_2 h_15_1_3 h_15_1_4 h_15_2_0 h_15_2_1 h_15_2_2 h_15_2_3 h_15_2_4 h_15_3_0 h_15_3_1 h_15_3_2 h_15_3_3 h_15_3_4 h_15_4_0 h_15_4_1 h_15_4_2 h_15_4_3 h_15_4_4
    have h_16 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_16 h_P
      (array_ext_25 h_state_size_15)
    simp only [Nat.reduceAdd] at h_16
    simp [
      h_15_0_0, h_15_0_1, h_15_0_2, h_15_0_3, h_15_0_4,
      h_15_1_0, h_15_1_1, h_15_1_2, h_15_1_3, h_15_1_4,
      h_15_2_0, h_15_2_1, h_15_2_2, h_15_2_3, h_15_2_4,
      h_15_3_0, h_15_3_1, h_15_3_2, h_15_3_3, h_15_3_4,
      h_15_4_0, h_15_4_1, h_15_4_2, h_15_4_3, h_15_4_4,
    ] at h_16
    clear h_15_0_0 h_15_0_1 h_15_0_2 h_15_0_3 h_15_0_4
    clear h_15_1_0 h_15_1_1 h_15_1_2 h_15_1_3 h_15_1_4
    clear h_15_2_0 h_15_2_1 h_15_2_2 h_15_2_3 h_15_2_4
    clear h_15_3_0 h_15_3_1 h_15_3_2 h_15_3_3 h_15_3_4
    clear h_15_4_0 h_15_4_1 h_15_4_2 h_15_4_3 h_15_4_4
    clear h_15 h_range_15
    have h_next_row_17 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨17, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_17
    simp [h_next_row_17] at h_16
    have h_range_16 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_15]
      omega
    simp [Array.getElem?_eq_getElem, h_range_16] at h_16
    have h_state_size_16 := keccak_round_size h_state_size_15 (round := 16)
    have h_mem_17: 17 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_16_0_0 := h_16 0 0
    have h_16_0_1 := h_16 0 1
    have h_16_0_2 := h_16 0 2
    have h_16_0_3 := h_16 0 3
    have h_16_0_4 := h_16 0 4
    have h_16_1_0 := h_16 1 0
    have h_16_1_1 := h_16 1 1
    have h_16_1_2 := h_16 1 2
    have h_16_1_3 := h_16 1 3
    have h_16_1_4 := h_16 1 4
    have h_16_2_0 := h_16 2 0
    have h_16_2_1 := h_16 2 1
    have h_16_2_2 := h_16 2 2
    have h_16_2_3 := h_16 2 3
    have h_16_2_4 := h_16 2 4
    have h_16_3_0 := h_16 3 0
    have h_16_3_1 := h_16 3 1
    have h_16_3_2 := h_16 3 2
    have h_16_3_3 := h_16 3 3
    have h_16_3_4 := h_16 3 4
    have h_16_4_0 := h_16 4 0
    have h_16_4_1 := h_16 4 1
    have h_16_4_2 := h_16 4 2
    have h_16_4_3 := h_16 4 3
    have h_16_4_4 := h_16 4 4
    simp [fin_vals] at h_16_0_0 h_16_0_1 h_16_0_2 h_16_0_3 h_16_0_4 h_16_1_0 h_16_1_1 h_16_1_2 h_16_1_3 h_16_1_4 h_16_2_0 h_16_2_1 h_16_2_2 h_16_2_3 h_16_2_4 h_16_3_0 h_16_3_1 h_16_3_2 h_16_3_3 h_16_3_4 h_16_4_0 h_16_4_1 h_16_4_2 h_16_4_3 h_16_4_4
    have h_17 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_17 h_P
      (array_ext_25 h_state_size_16)
    simp only [Nat.reduceAdd] at h_17
    simp [
      h_16_0_0, h_16_0_1, h_16_0_2, h_16_0_3, h_16_0_4,
      h_16_1_0, h_16_1_1, h_16_1_2, h_16_1_3, h_16_1_4,
      h_16_2_0, h_16_2_1, h_16_2_2, h_16_2_3, h_16_2_4,
      h_16_3_0, h_16_3_1, h_16_3_2, h_16_3_3, h_16_3_4,
      h_16_4_0, h_16_4_1, h_16_4_2, h_16_4_3, h_16_4_4,
    ] at h_17
    clear h_16_0_0 h_16_0_1 h_16_0_2 h_16_0_3 h_16_0_4
    clear h_16_1_0 h_16_1_1 h_16_1_2 h_16_1_3 h_16_1_4
    clear h_16_2_0 h_16_2_1 h_16_2_2 h_16_2_3 h_16_2_4
    clear h_16_3_0 h_16_3_1 h_16_3_2 h_16_3_3 h_16_3_4
    clear h_16_4_0 h_16_4_1 h_16_4_2 h_16_4_3 h_16_4_4
    clear h_16 h_range_16
    have h_next_row_18 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨18, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_18
    simp [h_next_row_18] at h_17
    have h_range_17 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 17
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_16]
      omega
    simp [Array.getElem?_eq_getElem, h_range_17] at h_17
    have h_state_size_17 := keccak_round_size h_state_size_16 (round := 17)
    have h_mem_18: 18 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_17_0_0 := h_17 0 0
    have h_17_0_1 := h_17 0 1
    have h_17_0_2 := h_17 0 2
    have h_17_0_3 := h_17 0 3
    have h_17_0_4 := h_17 0 4
    have h_17_1_0 := h_17 1 0
    have h_17_1_1 := h_17 1 1
    have h_17_1_2 := h_17 1 2
    have h_17_1_3 := h_17 1 3
    have h_17_1_4 := h_17 1 4
    have h_17_2_0 := h_17 2 0
    have h_17_2_1 := h_17 2 1
    have h_17_2_2 := h_17 2 2
    have h_17_2_3 := h_17 2 3
    have h_17_2_4 := h_17 2 4
    have h_17_3_0 := h_17 3 0
    have h_17_3_1 := h_17 3 1
    have h_17_3_2 := h_17 3 2
    have h_17_3_3 := h_17 3 3
    have h_17_3_4 := h_17 3 4
    have h_17_4_0 := h_17 4 0
    have h_17_4_1 := h_17 4 1
    have h_17_4_2 := h_17 4 2
    have h_17_4_3 := h_17 4 3
    have h_17_4_4 := h_17 4 4
    simp [fin_vals] at h_17_0_0 h_17_0_1 h_17_0_2 h_17_0_3 h_17_0_4 h_17_1_0 h_17_1_1 h_17_1_2 h_17_1_3 h_17_1_4 h_17_2_0 h_17_2_1 h_17_2_2 h_17_2_3 h_17_2_4 h_17_3_0 h_17_3_1 h_17_3_2 h_17_3_3 h_17_3_4 h_17_4_0 h_17_4_1 h_17_4_2 h_17_4_3 h_17_4_4
    have h_18 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_18 h_P
      (array_ext_25 h_state_size_17)
    simp only [Nat.reduceAdd] at h_18
    simp [
      h_17_0_0, h_17_0_1, h_17_0_2, h_17_0_3, h_17_0_4,
      h_17_1_0, h_17_1_1, h_17_1_2, h_17_1_3, h_17_1_4,
      h_17_2_0, h_17_2_1, h_17_2_2, h_17_2_3, h_17_2_4,
      h_17_3_0, h_17_3_1, h_17_3_2, h_17_3_3, h_17_3_4,
      h_17_4_0, h_17_4_1, h_17_4_2, h_17_4_3, h_17_4_4,
    ] at h_18
    clear h_17_0_0 h_17_0_1 h_17_0_2 h_17_0_3 h_17_0_4
    clear h_17_1_0 h_17_1_1 h_17_1_2 h_17_1_3 h_17_1_4
    clear h_17_2_0 h_17_2_1 h_17_2_2 h_17_2_3 h_17_2_4
    clear h_17_3_0 h_17_3_1 h_17_3_2 h_17_3_3 h_17_3_4
    clear h_17_4_0 h_17_4_1 h_17_4_2 h_17_4_3 h_17_4_4
    clear h_17 h_range_17
    have h_next_row_19 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨19, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_19
    simp [h_next_row_19] at h_18
    have h_range_18 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 18
      (LeanCrypto.HashFunctions.keccak_round 17
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_17]
      omega
    simp [Array.getElem?_eq_getElem, h_range_18] at h_18
    have h_state_size_18 := keccak_round_size h_state_size_17 (round := 18)
    have h_mem_19: 19 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_18_0_0 := h_18 0 0
    have h_18_0_1 := h_18 0 1
    have h_18_0_2 := h_18 0 2
    have h_18_0_3 := h_18 0 3
    have h_18_0_4 := h_18 0 4
    have h_18_1_0 := h_18 1 0
    have h_18_1_1 := h_18 1 1
    have h_18_1_2 := h_18 1 2
    have h_18_1_3 := h_18 1 3
    have h_18_1_4 := h_18 1 4
    have h_18_2_0 := h_18 2 0
    have h_18_2_1 := h_18 2 1
    have h_18_2_2 := h_18 2 2
    have h_18_2_3 := h_18 2 3
    have h_18_2_4 := h_18 2 4
    have h_18_3_0 := h_18 3 0
    have h_18_3_1 := h_18 3 1
    have h_18_3_2 := h_18 3 2
    have h_18_3_3 := h_18 3 3
    have h_18_3_4 := h_18 3 4
    have h_18_4_0 := h_18 4 0
    have h_18_4_1 := h_18 4 1
    have h_18_4_2 := h_18 4 2
    have h_18_4_3 := h_18 4 3
    have h_18_4_4 := h_18 4 4
    simp [fin_vals] at h_18_0_0 h_18_0_1 h_18_0_2 h_18_0_3 h_18_0_4 h_18_1_0 h_18_1_1 h_18_1_2 h_18_1_3 h_18_1_4 h_18_2_0 h_18_2_1 h_18_2_2 h_18_2_3 h_18_2_4 h_18_3_0 h_18_3_1 h_18_3_2 h_18_3_3 h_18_3_4 h_18_4_0 h_18_4_1 h_18_4_2 h_18_4_3 h_18_4_4
    have h_19 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_19 h_P
      (array_ext_25 h_state_size_18)
    simp only [Nat.reduceAdd] at h_19
    simp [
      h_18_0_0, h_18_0_1, h_18_0_2, h_18_0_3, h_18_0_4,
      h_18_1_0, h_18_1_1, h_18_1_2, h_18_1_3, h_18_1_4,
      h_18_2_0, h_18_2_1, h_18_2_2, h_18_2_3, h_18_2_4,
      h_18_3_0, h_18_3_1, h_18_3_2, h_18_3_3, h_18_3_4,
      h_18_4_0, h_18_4_1, h_18_4_2, h_18_4_3, h_18_4_4,
    ] at h_19
    clear h_18_0_0 h_18_0_1 h_18_0_2 h_18_0_3 h_18_0_4
    clear h_18_1_0 h_18_1_1 h_18_1_2 h_18_1_3 h_18_1_4
    clear h_18_2_0 h_18_2_1 h_18_2_2 h_18_2_3 h_18_2_4
    clear h_18_3_0 h_18_3_1 h_18_3_2 h_18_3_3 h_18_3_4
    clear h_18_4_0 h_18_4_1 h_18_4_2 h_18_4_3 h_18_4_4
    clear h_18 h_range_18
    have h_next_row_20 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨20, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_20
    simp [h_next_row_20] at h_19
    have h_range_19 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 19
      (LeanCrypto.HashFunctions.keccak_round 18
      (LeanCrypto.HashFunctions.keccak_round 17
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_18]
      omega
    simp [Array.getElem?_eq_getElem, h_range_19] at h_19
    have h_state_size_19 := keccak_round_size h_state_size_18 (round := 19)
    have h_mem_20: 20 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_19_0_0 := h_19 0 0
    have h_19_0_1 := h_19 0 1
    have h_19_0_2 := h_19 0 2
    have h_19_0_3 := h_19 0 3
    have h_19_0_4 := h_19 0 4
    have h_19_1_0 := h_19 1 0
    have h_19_1_1 := h_19 1 1
    have h_19_1_2 := h_19 1 2
    have h_19_1_3 := h_19 1 3
    have h_19_1_4 := h_19 1 4
    have h_19_2_0 := h_19 2 0
    have h_19_2_1 := h_19 2 1
    have h_19_2_2 := h_19 2 2
    have h_19_2_3 := h_19 2 3
    have h_19_2_4 := h_19 2 4
    have h_19_3_0 := h_19 3 0
    have h_19_3_1 := h_19 3 1
    have h_19_3_2 := h_19 3 2
    have h_19_3_3 := h_19 3 3
    have h_19_3_4 := h_19 3 4
    have h_19_4_0 := h_19 4 0
    have h_19_4_1 := h_19 4 1
    have h_19_4_2 := h_19 4 2
    have h_19_4_3 := h_19 4 3
    have h_19_4_4 := h_19 4 4
    simp [fin_vals] at h_19_0_0 h_19_0_1 h_19_0_2 h_19_0_3 h_19_0_4 h_19_1_0 h_19_1_1 h_19_1_2 h_19_1_3 h_19_1_4 h_19_2_0 h_19_2_1 h_19_2_2 h_19_2_3 h_19_2_4 h_19_3_0 h_19_3_1 h_19_3_2 h_19_3_3 h_19_3_4 h_19_4_0 h_19_4_1 h_19_4_2 h_19_4_3 h_19_4_4
    have h_20 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_20 h_P
      (array_ext_25 h_state_size_19)
    simp only [Nat.reduceAdd] at h_20
    simp [
      h_19_0_0, h_19_0_1, h_19_0_2, h_19_0_3, h_19_0_4,
      h_19_1_0, h_19_1_1, h_19_1_2, h_19_1_3, h_19_1_4,
      h_19_2_0, h_19_2_1, h_19_2_2, h_19_2_3, h_19_2_4,
      h_19_3_0, h_19_3_1, h_19_3_2, h_19_3_3, h_19_3_4,
      h_19_4_0, h_19_4_1, h_19_4_2, h_19_4_3, h_19_4_4,
    ] at h_20
    clear h_19_0_0 h_19_0_1 h_19_0_2 h_19_0_3 h_19_0_4
    clear h_19_1_0 h_19_1_1 h_19_1_2 h_19_1_3 h_19_1_4
    clear h_19_2_0 h_19_2_1 h_19_2_2 h_19_2_3 h_19_2_4
    clear h_19_3_0 h_19_3_1 h_19_3_2 h_19_3_3 h_19_3_4
    clear h_19_4_0 h_19_4_1 h_19_4_2 h_19_4_3 h_19_4_4
    clear h_19 h_range_19
    have h_next_row_21 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨21, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_21
    simp [h_next_row_21] at h_20
    have h_range_20 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 20
      (LeanCrypto.HashFunctions.keccak_round 19
      (LeanCrypto.HashFunctions.keccak_round 18
      (LeanCrypto.HashFunctions.keccak_round 17
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_19]
      omega
    simp [Array.getElem?_eq_getElem, h_range_20] at h_20
    have h_state_size_20 := keccak_round_size h_state_size_19 (round := 20)
    have h_mem_21: 21 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_20_0_0 := h_20 0 0
    have h_20_0_1 := h_20 0 1
    have h_20_0_2 := h_20 0 2
    have h_20_0_3 := h_20 0 3
    have h_20_0_4 := h_20 0 4
    have h_20_1_0 := h_20 1 0
    have h_20_1_1 := h_20 1 1
    have h_20_1_2 := h_20 1 2
    have h_20_1_3 := h_20 1 3
    have h_20_1_4 := h_20 1 4
    have h_20_2_0 := h_20 2 0
    have h_20_2_1 := h_20 2 1
    have h_20_2_2 := h_20 2 2
    have h_20_2_3 := h_20 2 3
    have h_20_2_4 := h_20 2 4
    have h_20_3_0 := h_20 3 0
    have h_20_3_1 := h_20 3 1
    have h_20_3_2 := h_20 3 2
    have h_20_3_3 := h_20 3 3
    have h_20_3_4 := h_20 3 4
    have h_20_4_0 := h_20 4 0
    have h_20_4_1 := h_20 4 1
    have h_20_4_2 := h_20 4 2
    have h_20_4_3 := h_20 4 3
    have h_20_4_4 := h_20 4 4
    simp [fin_vals] at h_20_0_0 h_20_0_1 h_20_0_2 h_20_0_3 h_20_0_4 h_20_1_0 h_20_1_1 h_20_1_2 h_20_1_3 h_20_1_4 h_20_2_0 h_20_2_1 h_20_2_2 h_20_2_3 h_20_2_4 h_20_3_0 h_20_3_1 h_20_3_2 h_20_3_3 h_20_3_4 h_20_4_0 h_20_4_1 h_20_4_2 h_20_4_3 h_20_4_4
    have h_21 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_21 h_P
      (array_ext_25 h_state_size_20)
    simp only [Nat.reduceAdd] at h_21
    simp [
      h_20_0_0, h_20_0_1, h_20_0_2, h_20_0_3, h_20_0_4,
      h_20_1_0, h_20_1_1, h_20_1_2, h_20_1_3, h_20_1_4,
      h_20_2_0, h_20_2_1, h_20_2_2, h_20_2_3, h_20_2_4,
      h_20_3_0, h_20_3_1, h_20_3_2, h_20_3_3, h_20_3_4,
      h_20_4_0, h_20_4_1, h_20_4_2, h_20_4_3, h_20_4_4,
    ] at h_21
    clear h_20_0_0 h_20_0_1 h_20_0_2 h_20_0_3 h_20_0_4
    clear h_20_1_0 h_20_1_1 h_20_1_2 h_20_1_3 h_20_1_4
    clear h_20_2_0 h_20_2_1 h_20_2_2 h_20_2_3 h_20_2_4
    clear h_20_3_0 h_20_3_1 h_20_3_2 h_20_3_3 h_20_3_4
    clear h_20_4_0 h_20_4_1 h_20_4_2 h_20_4_3 h_20_4_4
    clear h_20 h_range_20
    have h_next_row_22 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨22, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_22
    simp [h_next_row_22] at h_21
    have h_range_21 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 21
      (LeanCrypto.HashFunctions.keccak_round 20
      (LeanCrypto.HashFunctions.keccak_round 19
      (LeanCrypto.HashFunctions.keccak_round 18
      (LeanCrypto.HashFunctions.keccak_round 17
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state)))))))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_20]
      omega
    simp [Array.getElem?_eq_getElem, h_range_21] at h_21
    have h_state_size_21 := keccak_round_size h_state_size_20 (round := 21)
    have h_mem_22: 22 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_21_0_0 := h_21 0 0
    have h_21_0_1 := h_21 0 1
    have h_21_0_2 := h_21 0 2
    have h_21_0_3 := h_21 0 3
    have h_21_0_4 := h_21 0 4
    have h_21_1_0 := h_21 1 0
    have h_21_1_1 := h_21 1 1
    have h_21_1_2 := h_21 1 2
    have h_21_1_3 := h_21 1 3
    have h_21_1_4 := h_21 1 4
    have h_21_2_0 := h_21 2 0
    have h_21_2_1 := h_21 2 1
    have h_21_2_2 := h_21 2 2
    have h_21_2_3 := h_21 2 3
    have h_21_2_4 := h_21 2 4
    have h_21_3_0 := h_21 3 0
    have h_21_3_1 := h_21 3 1
    have h_21_3_2 := h_21 3 2
    have h_21_3_3 := h_21 3 3
    have h_21_3_4 := h_21 3 4
    have h_21_4_0 := h_21 4 0
    have h_21_4_1 := h_21 4 1
    have h_21_4_2 := h_21 4 2
    have h_21_4_3 := h_21 4 3
    have h_21_4_4 := h_21 4 4
    simp [fin_vals] at h_21_0_0 h_21_0_1 h_21_0_2 h_21_0_3 h_21_0_4 h_21_1_0 h_21_1_1 h_21_1_2 h_21_1_3 h_21_1_4 h_21_2_0 h_21_2_1 h_21_2_2 h_21_2_3 h_21_2_4 h_21_3_0 h_21_3_1 h_21_3_2 h_21_3_3 h_21_3_4 h_21_4_0 h_21_4_1 h_21_4_2 h_21_4_3 h_21_4_4
    have h_22 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_22 h_P
      (array_ext_25 h_state_size_21)
    simp only [Nat.reduceAdd] at h_22
    simp [
      h_21_0_0, h_21_0_1, h_21_0_2, h_21_0_3, h_21_0_4,
      h_21_1_0, h_21_1_1, h_21_1_2, h_21_1_3, h_21_1_4,
      h_21_2_0, h_21_2_1, h_21_2_2, h_21_2_3, h_21_2_4,
      h_21_3_0, h_21_3_1, h_21_3_2, h_21_3_3, h_21_3_4,
      h_21_4_0, h_21_4_1, h_21_4_2, h_21_4_3, h_21_4_4,
    ] at h_22
    clear h_21_0_0 h_21_0_1 h_21_0_2 h_21_0_3 h_21_0_4
    clear h_21_1_0 h_21_1_1 h_21_1_2 h_21_1_3 h_21_1_4
    clear h_21_2_0 h_21_2_1 h_21_2_2 h_21_2_3 h_21_2_4
    clear h_21_3_0 h_21_3_1 h_21_3_2 h_21_3_3 h_21_3_4
    clear h_21_4_0 h_21_4_1 h_21_4_2 h_21_4_3 h_21_4_4
    clear h_21 h_range_21
    have h_next_row_23 (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨23, by trivial⟩ i j
    simp [next_row_check.eq_def] at h_next_row_23
    simp [h_next_row_23] at h_22
    have h_range_22 (x y: Fin 5):
      y.val*5+x.val <
      (LeanCrypto.HashFunctions.keccak_round 22
      (LeanCrypto.HashFunctions.keccak_round 21
      (LeanCrypto.HashFunctions.keccak_round 20
      (LeanCrypto.HashFunctions.keccak_round 19
      (LeanCrypto.HashFunctions.keccak_round 18
      (LeanCrypto.HashFunctions.keccak_round 17
      (LeanCrypto.HashFunctions.keccak_round 16
      (LeanCrypto.HashFunctions.keccak_round 15
      (LeanCrypto.HashFunctions.keccak_round 14
      (LeanCrypto.HashFunctions.keccak_round 13
      (LeanCrypto.HashFunctions.keccak_round 12
      (LeanCrypto.HashFunctions.keccak_round 11
      (LeanCrypto.HashFunctions.keccak_round 10
      (LeanCrypto.HashFunctions.keccak_round 9
      (LeanCrypto.HashFunctions.keccak_round 8
      (LeanCrypto.HashFunctions.keccak_round 7
      (LeanCrypto.HashFunctions.keccak_round 6
      (LeanCrypto.HashFunctions.keccak_round 5
      (LeanCrypto.HashFunctions.keccak_round 4
      (LeanCrypto.HashFunctions.keccak_round 3
      (LeanCrypto.HashFunctions.keccak_round 2
      (LeanCrypto.HashFunctions.keccak_round 1
      (LeanCrypto.HashFunctions.keccak_round 0 state))))))))))))))))))))))).size
    := by
      rewrite [keccak_round_size h_state_size_21]
      omega
    simp [Array.getElem?_eq_getElem, h_range_22] at h_22
    have h_state_size_22 := keccak_round_size h_state_size_21 (round := 22)
    have h_mem_23: 23 ∈ Finset.Icc 0 23 := by
      rewrite [Finset.mem_Icc]
      omega
    have h_22_0_0 := h_22 0 0
    have h_22_0_1 := h_22 0 1
    have h_22_0_2 := h_22 0 2
    have h_22_0_3 := h_22 0 3
    have h_22_0_4 := h_22 0 4
    have h_22_1_0 := h_22 1 0
    have h_22_1_1 := h_22 1 1
    have h_22_1_2 := h_22 1 2
    have h_22_1_3 := h_22 1 3
    have h_22_1_4 := h_22 1 4
    have h_22_2_0 := h_22 2 0
    have h_22_2_1 := h_22 2 1
    have h_22_2_2 := h_22 2 2
    have h_22_2_3 := h_22 2 3
    have h_22_2_4 := h_22 2 4
    have h_22_3_0 := h_22 3 0
    have h_22_3_1 := h_22 3 1
    have h_22_3_2 := h_22 3 2
    have h_22_3_3 := h_22 3 3
    have h_22_3_4 := h_22 3 4
    have h_22_4_0 := h_22 4 0
    have h_22_4_1 := h_22 4 1
    have h_22_4_2 := h_22 4 2
    have h_22_4_3 := h_22 4 3
    have h_22_4_4 := h_22 4 4
    simp [fin_vals] at h_22_0_0 h_22_0_1 h_22_0_2 h_22_0_3 h_22_0_4 h_22_1_0 h_22_1_1 h_22_1_2 h_22_1_3 h_22_1_4 h_22_2_0 h_22_2_1 h_22_2_2 h_22_2_3 h_22_2_4 h_22_3_0 h_22_3_1 h_22_3_2 h_22_3_3 h_22_3_4 h_22_4_0 h_22_4_1 h_22_4_2 h_22_4_3 h_22_4_4
    have h_23 (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
      h_meets_constraints h_mem_23 h_P
      (array_ext_25 h_state_size_22)
    simp only [Nat.reduceAdd] at h_23
    simp [
      h_22_0_0, h_22_0_1, h_22_0_2, h_22_0_3, h_22_0_4,
      h_22_1_0, h_22_1_1, h_22_1_2, h_22_1_3, h_22_1_4,
      h_22_2_0, h_22_2_1, h_22_2_2, h_22_2_3, h_22_2_4,
      h_22_3_0, h_22_3_1, h_22_3_2, h_22_3_3, h_22_3_4,
      h_22_4_0, h_22_4_1, h_22_4_2, h_22_4_3, h_22_4_4,
    ] at h_23
    exact h_23 x y
    done













    -- clear h_X_0_0 h_X_0_1 h_X_0_2 h_X_0_3 h_X_0_4
    -- clear h_X_1_0 h_X_1_1 h_X_1_2 h_X_1_3 h_X_1_4
    -- clear h_X_2_0 h_X_2_1 h_X_2_2 h_X_2_3 h_X_2_4
    -- clear h_X_3_0 h_X_3_1 h_X_3_2 h_X_3_3 h_X_3_4
    -- clear h_X_4_0 h_X_4_1 h_X_4_2 h_X_4_3 h_X_4_4
    -- clear h_X h_range_X
    -- have h_next_row_Z (i j) := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨Z, by trivial⟩ i j
    -- simp [next_row_check.eq_def] at h_next_row_Z
    -- simp [h_next_row_Z] at h_Y
    -- have h_range_Y (x y: Fin 5):
    --   y.val*5+x.val <
    --   (LeanCrypto.HashFunctions.keccak_round 5
    --   (LeanCrypto.HashFunctions.keccak_round 4
    --   (LeanCrypto.HashFunctions.keccak_round 3
    --   (LeanCrypto.HashFunctions.keccak_round 2
    --   (LeanCrypto.HashFunctions.keccak_round 1
    --   (LeanCrypto.HashFunctions.keccak_round 0 state)))))).size
    -- := by
    --   rewrite [keccak_round_size h_state_size_X]
    --   omega
    -- simp [Array.getElem?_eq_getElem, h_range_Y] at h_Y
    -- have h_state_size_Y := keccak_round_size h_state_size_X (round := Y)
    -- have h_mem_Z: Z ∈ Finset.Icc 0 23 := by
    --   rewrite [Finset.mem_Icc]
    --   omega
    -- have h_Y_0_0 := h_Y 0 0
    -- have h_Y_0_1 := h_Y 0 1
    -- have h_Y_0_2 := h_Y 0 2
    -- have h_Y_0_3 := h_Y 0 3
    -- have h_Y_0_4 := h_Y 0 4
    -- have h_Y_1_0 := h_Y 1 0
    -- have h_Y_1_1 := h_Y 1 1
    -- have h_Y_1_2 := h_Y 1 2
    -- have h_Y_1_3 := h_Y 1 3
    -- have h_Y_1_4 := h_Y 1 4
    -- have h_Y_2_0 := h_Y 2 0
    -- have h_Y_2_1 := h_Y 2 1
    -- have h_Y_2_2 := h_Y 2 2
    -- have h_Y_2_3 := h_Y 2 3
    -- have h_Y_2_4 := h_Y 2 4
    -- have h_Y_3_0 := h_Y 3 0
    -- have h_Y_3_1 := h_Y 3 1
    -- have h_Y_3_2 := h_Y 3 2
    -- have h_Y_3_3 := h_Y 3 3
    -- have h_Y_3_4 := h_Y 3 4
    -- have h_Y_4_0 := h_Y 4 0
    -- have h_Y_4_1 := h_Y 4 1
    -- have h_Y_4_2 := h_Y 4 2
    -- have h_Y_4_3 := h_Y 4 3
    -- have h_Y_4_4 := h_Y 4 4
    -- simp [fin_vals] at h_Y_0_0 h_Y_0_1 h_Y_0_2 h_Y_0_3 h_Y_0_4 h_Y_1_0 h_Y_1_1 h_Y_1_2 h_Y_1_3 h_Y_1_4 h_Y_2_0 h_Y_2_1 h_Y_2_2 h_Y_2_3 h_Y_2_4 h_Y_3_0 h_Y_3_1 h_Y_3_2 h_Y_3_3 h_Y_3_4 h_Y_4_0 h_Y_4_1 h_Y_4_2 h_Y_4_3 h_Y_4_4
    -- have h_Z (x y: Fin 5) := iota_s_equiv (x := x) (y := y)
    --   h_meets_constraints h_mem_Z h_P
    --   (array_ext_25 h_state_size_Y)
    -- simp only [Nat.reduceAdd] at h_Z
    -- simp [
    --   h_Y_0_0, h_Y_0_1, h_Y_0_2, h_Y_0_3, h_Y_0_4,
    --   h_Y_1_0, h_Y_1_1, h_Y_1_2, h_Y_1_3, h_Y_1_4,
    --   h_Y_2_0, h_Y_2_1, h_Y_2_2, h_Y_2_3, h_Y_2_4,
    --   h_Y_3_0, h_Y_3_1, h_Y_3_2, h_Y_3_3, h_Y_3_4,
    --   h_Y_4_0, h_Y_4_1, h_Y_4_2, h_Y_4_3, h_Y_4_4,
    -- ] at h_Z






    --   h_meets_constraints this h_P
      -- (array_ext_25 h_state_size_0)
      -- (h_0 0 0) (h_0 1 0) (h_0 2 0) (h_0 3 0) (h_0 4 0)
      -- (h_0 0 1) (h_0 1 1) (h_0 2 1) (h_0 3 1) (h_0 4 1)
      -- (h_0 0 2) (h_0 1 2) (h_0 2 2) (h_0 3 2) (h_0 4 2)
      -- (h_0 0 3) (h_0 1 3) (h_0 2 3) (h_0 3 3) (h_0 4 3)
      -- (h_0 0 4) (h_0 1 4) (h_0 2 4) (h_0 3 4) (h_0 4 4)




end Keccak.Soundness

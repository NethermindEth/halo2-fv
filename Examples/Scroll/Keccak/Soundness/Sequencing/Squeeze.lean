import Examples.Scroll.Keccak.Soundness.Sequencing.KeccakF
import Examples.Scroll.Keccak.Lookups.PackTable.Lookups
import Examples.Scroll.Keccak.ProgramProofs.IsFinal
import Examples.Scroll.Keccak.ProgramProofs.Squeeze

namespace Keccak.Soundness

  lemma squeeze_from_equiv {c: ValidCircuit P P_Prime}
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
    (h_y: y < 4)
    (h_is_paddings: is_paddings c 17 (-1) = 1)
  :
    .some (squeeze_from c (24-y)).val =
    (LeanCrypto.HashFunctions.keccakF state)[y*5]?.map UInt64_to_unpacked_Nat
  := by
    have h_squeeze_verify_packed := Proofs.squeeze_verify_packed_of_meets_constraints h_meets_constraints ⟨y, h_y⟩
    unfold squeeze_verify_packed start_new_hash at h_squeeze_verify_packed
    have h_is_final := Proofs.is_final_eq_last_is_padding_of_meets_constraints h_meets_constraints
    unfold is_final_eq_last_is_padding last_is_padding_in_block at h_is_final
    simp [keccak_constants] at h_is_final
    simp [keccak_constants, h_is_final, h_is_paddings] at h_squeeze_verify_packed
    rewrite [←h_squeeze_verify_packed]
    have : hash_words c 25 ⟨y, h_y⟩ = s c 25 y 0 := by
      unfold hash_words
      by_cases y=0; simp_all
      by_cases y=1; simp_all
      by_cases y=2; simp_all
      by_cases y=3; simp_all
      exfalso; omega
    rewrite [this]
    have := iota_s_keccak_f_equiv h_meets_constraints h_P h_state
      h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
      h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
      h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
      h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
      h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
      (x := 0) (y := y)
    convert this using 3
    . have := Proofs.next_row_check_of_meets_constraints h_meets_constraints ⟨24, by {
        apply Finset.mem_Icc.mpr
        omega
      }⟩ y 0
      unfold next_row_check at this
      symm
      convert this
    . simp
      rw [Nat.mod_eq_of_lt (by omega)]

  lemma squeeze_from_decode_equiv {c: ValidCircuit P P_Prime}
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
    (h_y: y < 4)
    (h_is_paddings: is_paddings c 17 (-1) = 1):
    .some ((Decode.expr
      [(8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1680).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1681).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1682).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1683).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1684).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1685).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1686).val])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [(cell_manager c (24 - y) 1687).val]))]).val) =
    (LeanCrypto.HashFunctions.keccakF state)[y*5]?.map UInt64_to_unpacked_Nat
  := by
    have := Proofs.squeeze_bytes_of_meets_constraints h_meets_constraints ⟨(24-y), by {
      apply Finset.mem_Icc.mpr
      omega
    }⟩
    simp [
      squeeze_bytes.eq_def, Transform.split_expr.eq_def, Split.expr.eq_def,
      keccak_constants, Split.constraint.eq_def, Split.expr_res.eq_def,
      word_parts_known
    ] at this
    have ⟨⟨h_parts, h_decode⟩, h_transform⟩ := this
    clear this
    rewrite [←squeeze_from_equiv h_meets_constraints h_P h_state
      h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
      h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
      h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
      h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
      h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
      h_y h_is_paddings
    ]
    congr 1
    rewrite [←h_decode]
    rewrite [h_parts] at h_transform
    simp at h_transform
    have h_transform_1 := h_transform 8 (cell_manager c (24-y) 1668) 8 (cell_manager c (24-y) 1680)
    simp at h_transform_1
    replace h_transform_1 := Lookups.PackTable.apply_transform_table h_transform_1 (by omega)
    have h_transform_2 := h_transform 8 (cell_manager c (24-y) 1669) 8 (cell_manager c (24-y) 1681)
    simp at h_transform_2
    replace h_transform_2 := Lookups.PackTable.apply_transform_table h_transform_2 (by omega)
    have h_transform_3 := h_transform 8 (cell_manager c (24-y) 1670) 8 (cell_manager c (24-y) 1682)
    simp at h_transform_3
    replace h_transform_3 := Lookups.PackTable.apply_transform_table h_transform_3 (by omega)
    have h_transform_4 := h_transform 8 (cell_manager c (24-y) 1671) 8 (cell_manager c (24-y) 1683)
    simp at h_transform_4
    replace h_transform_4 := Lookups.PackTable.apply_transform_table h_transform_4 (by omega)
    have h_transform_5 := h_transform 8 (cell_manager c (24-y) 1672) 8 (cell_manager c (24-y) 1684)
    simp at h_transform_5
    replace h_transform_5 := Lookups.PackTable.apply_transform_table h_transform_5 (by omega)
    have h_transform_6 := h_transform 8 (cell_manager c (24-y) 1673) 8 (cell_manager c (24-y) 1685)
    simp at h_transform_6
    replace h_transform_6 := Lookups.PackTable.apply_transform_table h_transform_6 (by omega)
    have h_transform_7 := h_transform 8 (cell_manager c (24-y) 1674) 8 (cell_manager c (24-y) 1686)
    simp at h_transform_7
    replace h_transform_7 := Lookups.PackTable.apply_transform_table h_transform_7 (by omega)
    have h_transform_8 := h_transform 8 (cell_manager c (24-y) 1675) 8 (cell_manager c (24-y) 1687)
    simp at h_transform_8
    replace h_transform_8 := Lookups.PackTable.apply_transform_table h_transform_8 (by omega)
    rw [
      h_transform_1,
      h_transform_2,
      h_transform_3,
      h_transform_4,
      h_transform_5,
      h_transform_6,
      h_transform_7,
      h_transform_8
    ]

  set_option maxHeartbeats 400000
  lemma packtable_decode [NeZero P]
    (h_x1: x1 < 256)
    (h_x2: x2 < 256)
    (h_x3: x3 < 256)
    (h_x4: x4 < 256)
    (h_x5: x5 < 256)
    (h_x6: x6 < 256)
    (h_x7: x7 < 256)
    (h_x8: x8 < 256)
    (h:
      (Decode.expr [(8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x1])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x2])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x3])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x4])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x5])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x6])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x7])),
        (8, Lookups.PackTable.pack P (Lookups.PackTable.into_bits [x8]))]).val =
      UInt64_to_unpacked_Nat x
    )
    (h_P: P > Normalize.mask):
  x.toBitVec =
    BitVec.ofNat 8 x8 ++
    BitVec.ofNat 8 x7 ++
    BitVec.ofNat 8 x6 ++
    BitVec.ofNat 8 x5 ++
    BitVec.ofNat 8 x4 ++
    BitVec.ofNat 8 x3 ++
    BitVec.ofNat 8 x2 ++
    BitVec.ofNat 8 x1
  := by
    unfold Normalize.mask at h_P
    simp [
      Decode.expr, keccak_constants, mul_add,
      ←mul_assoc, ZMod.val_add, ZMod.val_mul,
      Lookups.PackTable.into_bits.eq_def, list_ops,
      Lookups.PackTable.pack.eq_def, Lookups.PackTable.pack_with_base.eq_def,
      zmod_pow_simps, add_mul
    ] at h
    have : ZMod.val (n := P) 8 = 2^3 := by
      rewrite [zmod_val_ofNat_of_lt]
      . decide
      . exact lt_of_le_of_lt (by trivial) h_P
    rewrite [this] at h; clear this
    have : ZMod.val (n := P) 16777216 = 2^24 := by
      rewrite [zmod_val_ofNat_of_lt]
      . decide
      . exact lt_of_le_of_lt (by trivial) h_P
    rewrite [this] at h; clear this
    simp only [
      ←pow_add, ←nat_shiftLeft_eq_mul_comm, Nat.reduceAdd,
      ←Nat.shiftLeft_eq, ←Nat.shiftLeft_add
    ] at h
    have h_mod (a: ℕ): a%2 ≤ 1 := by omega
    have h_mul (a b: ℕ) : a % 2 * b ≤ b := by
      exact le_trans (Nat.mul_le_mul (h_mod _) (by trivial)) (by simp)
    rewrite [Nat.mod_eq_of_lt] at h
    . simp [UInt64_to_unpacked_Nat, ←Nat.and_one_is_mod] at h
      rewrite [show x1 = (BitVec.setWidth 192 (BitVec.ofNat 8 x1)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x2 = (BitVec.setWidth 192 (BitVec.ofNat 8 x2)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x3 = (BitVec.setWidth 192 (BitVec.ofNat 8 x3)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x4 = (BitVec.setWidth 192 (BitVec.ofNat 8 x4)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x5 = (BitVec.setWidth 192 (BitVec.ofNat 8 x5)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x6 = (BitVec.setWidth 192 (BitVec.ofNat 8 x6)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x7 = (BitVec.setWidth 192 (BitVec.ofNat 8 x7)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show x8 = (BitVec.setWidth 192 (BitVec.ofNat 8 x8)).toNat by simp (disch := omega) [Nat.mod_eq_of_lt]] at h
      rewrite [show 128 = (128#192).toNat by decide] at h
      have (a: ℕ) : a / 64 = a / (64#192).toNat := by aesop
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _] at h
      rewrite [show 32 = (32#192).toNat by decide] at h
      rewrite [show 16 = (16#192).toNat by decide] at h
      rewrite [show 8 = (8#192).toNat by decide] at h
      rewrite [show 4 = (4#192).toNat by decide] at h
      have (a: ℕ) : a / 2 = a / (2#192).toNat := by aesop
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _] at h
      rewrite [show 1 = (1#192).toNat by decide] at h
      simp only [←BitVec.toNat_udiv, ←BitVec.toNat_and] at h
      rewrite [show (8#192).toNat = 8 by decide] at h
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 189 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 186 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 183 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 180 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 177 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 174 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 171 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 168 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 189 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 186 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 183 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 180 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 177 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 174 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 171 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 168).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x8] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 165 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 162 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 159 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 156 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 153 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 150 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 147 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 144 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 165 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 162 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 159 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 156 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 153 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 150 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 147 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 144).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x7] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 141 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 138 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 135 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 132 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 129 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 126 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 123 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 120 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 141 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 138 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 135 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 132 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 129 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 126 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 123 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 120).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x6] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 117 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 114 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 111 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 108 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 105 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 102 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 99 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 96 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 117 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 114 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 111 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 108 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 105 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 102 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 99 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 96).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x5] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 93 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 90 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 87 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 84 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 81 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 78 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 75 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 72 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 93 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 90 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 87 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 84 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 81 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 78 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 75 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 72).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x4] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 69 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 66 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 63 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 60 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 57 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 54 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 51 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 48 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 69 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 66 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 63 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 60 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 57 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 54 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 51 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 48).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x3] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 45 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 42 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 39 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 36 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 33 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 30 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 27 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 24 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 45 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 42 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 39 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 36 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 33 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 30 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 27 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 24).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x2] at h; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 21 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 18 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 15 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 12 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 9 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 6 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 3 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 21 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 18 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 15 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 12 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 9 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 6 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 3 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192)).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mod _)) _
        decide
      rewrite [this _ h_x1] at h; clear this
      rewrite [
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_eq
      ] at h
      simp [list_ops] at h
      bv_decide
    . apply lt_of_le_of_lt _ h_P
      simp [Nat.shiftLeft_eq]
      clear h
      convert Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add
                    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _))
                    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
                  (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
                (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
              (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
            (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mod _))

  lemma squeeze_bytes_equiv {c: ValidCircuit P P_Prime}
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
    (h_y: y < 4)
    (h_is_paddings: is_paddings c 17 (-1) = 1):
    .some (
      BitVec.ofNat 8 (cell_manager c (24 - y) 1687).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1686).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1685).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1684).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1683).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1682).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1681).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1680).val
    ) =
    (LeanCrypto.HashFunctions.keccakF state)[y*5]?.map UInt64.toBitVec
  := by
    have h_decode := squeeze_from_decode_equiv
      h_meets_constraints h_P h_state
      h_s_0_0 h_s_0_1 h_s_0_2 h_s_0_3 h_s_0_4
      h_s_1_0 h_s_1_1 h_s_1_2 h_s_1_3 h_s_1_4
      h_s_2_0 h_s_2_1 h_s_2_2 h_s_2_3 h_s_2_4
      h_s_3_0 h_s_3_1 h_s_3_2 h_s_3_3 h_s_3_4
      h_s_4_0 h_s_4_1 h_s_4_2 h_s_4_3 h_s_4_4
      h_y h_is_paddings
    symm at h_decode
    apply Option.map_eq_some'.mp at h_decode
    obtain ⟨val, ⟨h_some, h_decode⟩⟩ := h_decode
    simp [h_some]
    symm
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_table (x y: ZMod P) (h: ∃ lookup_row, Lookups.PackTable.transform_table P lookup_row = (x, y)):
      y.val < 256
    := by
      unfold Lookups.PackTable.transform_table at h
      obtain ⟨row, h_row⟩ := h
      split_ifs at h_row
      . simp at h_row
        rewrite [←h_row.2]
        simp
        rewrite [Nat.mod_eq_of_lt (by omega)]
        assumption
      . simp at h_row
        rewrite [←h_row.2]
        simp
    have h_squeeze_bytes := Proofs.squeeze_bytes_of_meets_constraints h_meets_constraints ⟨(24-y), by apply Finset.mem_Icc.mpr; omega⟩
    simp [
      squeeze_bytes, Transform.split_expr, squeeze_from_parts, keccak_constants,
      Split.expr, Split.expr_res, Split.constraint, word_parts_known
    ] at h_squeeze_bytes
    rw [packtable_decode (h := h_decode.symm)]
    . exact h_table (h := h_squeeze_bytes.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.2.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.2.2.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.2.2.2.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.2.2.2.2.2.1)
    . exact h_table (h := h_squeeze_bytes.2.2.2.2.2.2.2.2)
    . unfold Normalize.mask
      omega

end Keccak.Soundness

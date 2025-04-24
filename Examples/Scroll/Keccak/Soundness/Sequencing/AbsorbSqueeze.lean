import Examples.Scroll.Keccak.Soundness.Sequencing.Padding
import Examples.Scroll.Keccak.Soundness.Sequencing.StateArray

namespace Keccak.Soundness
  -- def state_bytes (c: ValidCircuit P P_Prime): ByteArray := sorry

  lemma array_range_8: Array.range 8 = #[0,1,2,3,4,5,6,7] := rfl

  lemma absorb_bytes_eval (state_bytes: ByteArray)
    (h_state_bytes: state_bytes = ⟨#[
      a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,
      a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,
      a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,
      a30,a31,a32,a33,a34,a35,a36,a37,a38,a39,
      a40,a41,a42,a43,a44,a45,a46,a47,a48,a49,
      a50,a51,a52,a53,a54,a55,a56,a57,a58,a59,
      a60,a61,a62,a63,a64,a65,a66,a67,a68,a69,
      a70,a71,a72,a73,a74,a75,a76,a77,a78,a79,
      a80,a81,a82,a83,a84,a85,a86,a87,a88,a89,
      a90,a91,a92,a93,a94,a95,a96,a97,a98,a99,
      a100,a101,a102,a103,a104,a105,a106,a107,a108,a109,
      a110,a111,a112,a113,a114,a115,a116,a117,a118,a119,
      a120,a121,a122,a123,a124,a125,a126,a127,a128,a129,
      a130,a131,a132,a133,a134,a135,
    ]⟩)
  :
    LeanCrypto.HashFunctions.Absorb.absorb 1088 (by trivial) (state_bytes) =
    LeanCrypto.HashFunctions.keccakF
    #[a0.toUInt64 <<< 0 ^^^ a1.toUInt64 <<< 8 ^^^ a2.toUInt64 <<< 16 ^^^ a3.toUInt64 <<< 24 ^^^ a4.toUInt64 <<< 32 ^^^
            a5.toUInt64 <<< 40 ^^^
          a6.toUInt64 <<< 48 ^^^
        a7.toUInt64 <<< 56,
      a40.toUInt64 <<< 0 ^^^ a41.toUInt64 <<< 8 ^^^ a42.toUInt64 <<< 16 ^^^ a43.toUInt64 <<< 24 ^^^
              a44.toUInt64 <<< 32 ^^^
            a45.toUInt64 <<< 40 ^^^
          a46.toUInt64 <<< 48 ^^^
        a47.toUInt64 <<< 56,
      a80.toUInt64 <<< 0 ^^^ a81.toUInt64 <<< 8 ^^^ a82.toUInt64 <<< 16 ^^^ a83.toUInt64 <<< 24 ^^^
              a84.toUInt64 <<< 32 ^^^
            a85.toUInt64 <<< 40 ^^^
          a86.toUInt64 <<< 48 ^^^
        a87.toUInt64 <<< 56,
      a120.toUInt64 <<< 0 ^^^ a121.toUInt64 <<< 8 ^^^ a122.toUInt64 <<< 16 ^^^ a123.toUInt64 <<< 24 ^^^
              a124.toUInt64 <<< 32 ^^^
            a125.toUInt64 <<< 40 ^^^
          a126.toUInt64 <<< 48 ^^^
        a127.toUInt64 <<< 56,
      0,
      a8.toUInt64 <<< 0 ^^^ a9.toUInt64 <<< 8 ^^^ a10.toUInt64 <<< 16 ^^^ a11.toUInt64 <<< 24 ^^^
              a12.toUInt64 <<< 32 ^^^
            a13.toUInt64 <<< 40 ^^^
          a14.toUInt64 <<< 48 ^^^
        a15.toUInt64 <<< 56,
      a48.toUInt64 <<< 0 ^^^ a49.toUInt64 <<< 8 ^^^ a50.toUInt64 <<< 16 ^^^ a51.toUInt64 <<< 24 ^^^
              a52.toUInt64 <<< 32 ^^^
            a53.toUInt64 <<< 40 ^^^
          a54.toUInt64 <<< 48 ^^^
        a55.toUInt64 <<< 56,
      a88.toUInt64 <<< 0 ^^^ a89.toUInt64 <<< 8 ^^^ a90.toUInt64 <<< 16 ^^^ a91.toUInt64 <<< 24 ^^^
              a92.toUInt64 <<< 32 ^^^
            a93.toUInt64 <<< 40 ^^^
          a94.toUInt64 <<< 48 ^^^
        a95.toUInt64 <<< 56,
      a128.toUInt64 <<< 0 ^^^ a129.toUInt64 <<< 8 ^^^ a130.toUInt64 <<< 16 ^^^ a131.toUInt64 <<< 24 ^^^
              a132.toUInt64 <<< 32 ^^^
            a133.toUInt64 <<< 40 ^^^
          a134.toUInt64 <<< 48 ^^^
        a135.toUInt64 <<< 56,
      0,
      a16.toUInt64 <<< 0 ^^^ a17.toUInt64 <<< 8 ^^^ a18.toUInt64 <<< 16 ^^^ a19.toUInt64 <<< 24 ^^^
              a20.toUInt64 <<< 32 ^^^
            a21.toUInt64 <<< 40 ^^^
          a22.toUInt64 <<< 48 ^^^
        a23.toUInt64 <<< 56,
      a56.toUInt64 <<< 0 ^^^ a57.toUInt64 <<< 8 ^^^ a58.toUInt64 <<< 16 ^^^ a59.toUInt64 <<< 24 ^^^
              a60.toUInt64 <<< 32 ^^^
            a61.toUInt64 <<< 40 ^^^
          a62.toUInt64 <<< 48 ^^^
        a63.toUInt64 <<< 56,
      a96.toUInt64 <<< 0 ^^^ a97.toUInt64 <<< 8 ^^^ a98.toUInt64 <<< 16 ^^^ a99.toUInt64 <<< 24 ^^^
              a100.toUInt64 <<< 32 ^^^
            a101.toUInt64 <<< 40 ^^^
          a102.toUInt64 <<< 48 ^^^
        a103.toUInt64 <<< 56,
      0, 0,
      a24.toUInt64 <<< 0 ^^^ a25.toUInt64 <<< 8 ^^^ a26.toUInt64 <<< 16 ^^^ a27.toUInt64 <<< 24 ^^^
              a28.toUInt64 <<< 32 ^^^
            a29.toUInt64 <<< 40 ^^^
          a30.toUInt64 <<< 48 ^^^
        a31.toUInt64 <<< 56,
      a64.toUInt64 <<< 0 ^^^ a65.toUInt64 <<< 8 ^^^ a66.toUInt64 <<< 16 ^^^ a67.toUInt64 <<< 24 ^^^
              a68.toUInt64 <<< 32 ^^^
            a69.toUInt64 <<< 40 ^^^
          a70.toUInt64 <<< 48 ^^^
        a71.toUInt64 <<< 56,
      a104.toUInt64 <<< 0 ^^^ a105.toUInt64 <<< 8 ^^^ a106.toUInt64 <<< 16 ^^^ a107.toUInt64 <<< 24 ^^^
              a108.toUInt64 <<< 32 ^^^
            a109.toUInt64 <<< 40 ^^^
          a110.toUInt64 <<< 48 ^^^
        a111.toUInt64 <<< 56,
      0, 0,
      a32.toUInt64 <<< 0 ^^^ a33.toUInt64 <<< 8 ^^^ a34.toUInt64 <<< 16 ^^^ a35.toUInt64 <<< 24 ^^^
              a36.toUInt64 <<< 32 ^^^
            a37.toUInt64 <<< 40 ^^^
          a38.toUInt64 <<< 48 ^^^
        a39.toUInt64 <<< 56,
      a72.toUInt64 <<< 0 ^^^ a73.toUInt64 <<< 8 ^^^ a74.toUInt64 <<< 16 ^^^ a75.toUInt64 <<< 24 ^^^
              a76.toUInt64 <<< 32 ^^^
            a77.toUInt64 <<< 40 ^^^
          a78.toUInt64 <<< 48 ^^^
        a79.toUInt64 <<< 56,
      a112.toUInt64 <<< 0 ^^^ a113.toUInt64 <<< 8 ^^^ a114.toUInt64 <<< 16 ^^^ a115.toUInt64 <<< 24 ^^^
              a116.toUInt64 <<< 32 ^^^
            a117.toUInt64 <<< 40 ^^^
          a118.toUInt64 <<< 48 ^^^
        a119.toUInt64 <<< 56,
      0, 0]
  := by
    simp [
      h_state_bytes,
      LeanCrypto.HashFunctions.Absorb.absorb
    ]
    simp [
      LeanCrypto.HashFunctions.Absorb.toBlocks,
      LeanCrypto.HashFunctions.Absorb.unfoldr,
      LeanCrypto.HashFunctions.Absorb.toBlocks.toLane,
      ByteArray.isEmpty,
      ByteArray.size,
      Array.splitAt,
      LeanCrypto.HashFunctions.Absorb.toBlocks.createWord64,
      LeanCrypto.HashFunctions.Absorb.ifoldl,
      array_range_8, uint64_zero_xor
    ]
    unfold LeanCrypto.HashFunctions.Absorb.absorbBlock
    simp
    unfold LeanCrypto.HashFunctions.Absorb.absorbBlock.state'
    simp [uint64_zero_xor]
    unfold LeanCrypto.HashFunctions.Absorb.absorbBlock
    simp

  lemma absorb_bytes_with_conversion_eval (state_bytes: ByteArray)
    (h_state_bytes: state_bytes = ⟨#[
      a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,
      a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,
      a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,
      a30,a31,a32,a33,a34,a35,a36,a37,a38,a39,
      a40,a41,a42,a43,a44,a45,a46,a47,a48,a49,
      a50,a51,a52,a53,a54,a55,a56,a57,a58,a59,
      a60,a61,a62,a63,a64,a65,a66,a67,a68,a69,
      a70,a71,a72,a73,a74,a75,a76,a77,a78,a79,
      a80,a81,a82,a83,a84,a85,a86,a87,a88,a89,
      a90,a91,a92,a93,a94,a95,a96,a97,a98,a99,
      a100,a101,a102,a103,a104,a105,a106,a107,a108,a109,
      a110,a111,a112,a113,a114,a115,a116,a117,a118,a119,
      a120,a121,a122,a123,a124,a125,a126,a127,a128,a129,
      a130,a131,a132,a133,a134,a135,
    ]⟩)
  :
    LeanCrypto.HashFunctions.Absorb.absorb
      1088
      (by trivial)
      (LeanCrypto.HashFunctions.byteArrayOfSHA3SR
        (LeanCrypto.HashFunctions.SHA3SRofByteArray state_bytes)
      ) =
    LeanCrypto.HashFunctions.keccakF #[a0.toUInt64 <<< 0 ^^^ a1.toUInt64 <<< 8 ^^^ a2.toUInt64 <<< 16 ^^^ a3.toUInt64 <<< 24 ^^^ a4.toUInt64 <<< 32 ^^^
            a5.toUInt64 <<< 40 ^^^
          a6.toUInt64 <<< 48 ^^^
        a7.toUInt64 <<< 56,
      a40.toUInt64 <<< 0 ^^^ a41.toUInt64 <<< 8 ^^^ a42.toUInt64 <<< 16 ^^^ a43.toUInt64 <<< 24 ^^^
              a44.toUInt64 <<< 32 ^^^
            a45.toUInt64 <<< 40 ^^^
          a46.toUInt64 <<< 48 ^^^
        a47.toUInt64 <<< 56,
      a80.toUInt64 <<< 0 ^^^ a81.toUInt64 <<< 8 ^^^ a82.toUInt64 <<< 16 ^^^ a83.toUInt64 <<< 24 ^^^
              a84.toUInt64 <<< 32 ^^^
            a85.toUInt64 <<< 40 ^^^
          a86.toUInt64 <<< 48 ^^^
        a87.toUInt64 <<< 56,
      a120.toUInt64 <<< 0 ^^^ a121.toUInt64 <<< 8 ^^^ a122.toUInt64 <<< 16 ^^^ a123.toUInt64 <<< 24 ^^^
              a124.toUInt64 <<< 32 ^^^
            a125.toUInt64 <<< 40 ^^^
          a126.toUInt64 <<< 48 ^^^
        a127.toUInt64 <<< 56,
      0,
      a8.toUInt64 <<< 0 ^^^ a9.toUInt64 <<< 8 ^^^ a10.toUInt64 <<< 16 ^^^ a11.toUInt64 <<< 24 ^^^
              a12.toUInt64 <<< 32 ^^^
            a13.toUInt64 <<< 40 ^^^
          a14.toUInt64 <<< 48 ^^^
        a15.toUInt64 <<< 56,
      a48.toUInt64 <<< 0 ^^^ a49.toUInt64 <<< 8 ^^^ a50.toUInt64 <<< 16 ^^^ a51.toUInt64 <<< 24 ^^^
              a52.toUInt64 <<< 32 ^^^
            a53.toUInt64 <<< 40 ^^^
          a54.toUInt64 <<< 48 ^^^
        a55.toUInt64 <<< 56,
      a88.toUInt64 <<< 0 ^^^ a89.toUInt64 <<< 8 ^^^ a90.toUInt64 <<< 16 ^^^ a91.toUInt64 <<< 24 ^^^
              a92.toUInt64 <<< 32 ^^^
            a93.toUInt64 <<< 40 ^^^
          a94.toUInt64 <<< 48 ^^^
        a95.toUInt64 <<< 56,
      a128.toUInt64 <<< 0 ^^^ a129.toUInt64 <<< 8 ^^^ a130.toUInt64 <<< 16 ^^^ a131.toUInt64 <<< 24 ^^^
              a132.toUInt64 <<< 32 ^^^
            a133.toUInt64 <<< 40 ^^^
          a134.toUInt64 <<< 48 ^^^
        a135.toUInt64 <<< 56,
      0,
      a16.toUInt64 <<< 0 ^^^ a17.toUInt64 <<< 8 ^^^ a18.toUInt64 <<< 16 ^^^ a19.toUInt64 <<< 24 ^^^
              a20.toUInt64 <<< 32 ^^^
            a21.toUInt64 <<< 40 ^^^
          a22.toUInt64 <<< 48 ^^^
        a23.toUInt64 <<< 56,
      a56.toUInt64 <<< 0 ^^^ a57.toUInt64 <<< 8 ^^^ a58.toUInt64 <<< 16 ^^^ a59.toUInt64 <<< 24 ^^^
              a60.toUInt64 <<< 32 ^^^
            a61.toUInt64 <<< 40 ^^^
          a62.toUInt64 <<< 48 ^^^
        a63.toUInt64 <<< 56,
      a96.toUInt64 <<< 0 ^^^ a97.toUInt64 <<< 8 ^^^ a98.toUInt64 <<< 16 ^^^ a99.toUInt64 <<< 24 ^^^
              a100.toUInt64 <<< 32 ^^^
            a101.toUInt64 <<< 40 ^^^
          a102.toUInt64 <<< 48 ^^^
        a103.toUInt64 <<< 56,
      0, 0,
      a24.toUInt64 <<< 0 ^^^ a25.toUInt64 <<< 8 ^^^ a26.toUInt64 <<< 16 ^^^ a27.toUInt64 <<< 24 ^^^
              a28.toUInt64 <<< 32 ^^^
            a29.toUInt64 <<< 40 ^^^
          a30.toUInt64 <<< 48 ^^^
        a31.toUInt64 <<< 56,
      a64.toUInt64 <<< 0 ^^^ a65.toUInt64 <<< 8 ^^^ a66.toUInt64 <<< 16 ^^^ a67.toUInt64 <<< 24 ^^^
              a68.toUInt64 <<< 32 ^^^
            a69.toUInt64 <<< 40 ^^^
          a70.toUInt64 <<< 48 ^^^
        a71.toUInt64 <<< 56,
      a104.toUInt64 <<< 0 ^^^ a105.toUInt64 <<< 8 ^^^ a106.toUInt64 <<< 16 ^^^ a107.toUInt64 <<< 24 ^^^
              a108.toUInt64 <<< 32 ^^^
            a109.toUInt64 <<< 40 ^^^
          a110.toUInt64 <<< 48 ^^^
        a111.toUInt64 <<< 56,
      0, 0,
      a32.toUInt64 <<< 0 ^^^ a33.toUInt64 <<< 8 ^^^ a34.toUInt64 <<< 16 ^^^ a35.toUInt64 <<< 24 ^^^
              a36.toUInt64 <<< 32 ^^^
            a37.toUInt64 <<< 40 ^^^
          a38.toUInt64 <<< 48 ^^^
        a39.toUInt64 <<< 56,
      a72.toUInt64 <<< 0 ^^^ a73.toUInt64 <<< 8 ^^^ a74.toUInt64 <<< 16 ^^^ a75.toUInt64 <<< 24 ^^^
              a76.toUInt64 <<< 32 ^^^
            a77.toUInt64 <<< 40 ^^^
          a78.toUInt64 <<< 48 ^^^
        a79.toUInt64 <<< 56,
      a112.toUInt64 <<< 0 ^^^ a113.toUInt64 <<< 8 ^^^ a114.toUInt64 <<< 16 ^^^ a115.toUInt64 <<< 24 ^^^
              a116.toUInt64 <<< 32 ^^^
            a117.toUInt64 <<< 40 ^^^
          a118.toUInt64 <<< 48 ^^^
        a119.toUInt64 <<< 56,
      0, 0]
  := by
    rewrite [sha3sr_of_bytearray _ (by simp [ByteArray.size, h_state_bytes])]
    rewrite [padded_data_sha3r_to_byte_array]
    rw [absorb_bytes_eval _ h_state_bytes]

  lemma squeeze_eval(h_bytes: bytes = #[
    a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,
    a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,
    a20,a21,a22,a23,a24
  ]):
    LeanCrypto.HashFunctions.squeeze' 1088 h 32 bytes =
    ⟨#[(a0 >>> 0).toUInt8, (a0 >>> 8).toUInt8, (a0 >>> 16).toUInt8, (a0 >>> 24).toUInt8, (a0 >>> 32).toUInt8,
        (a0 >>> 40).toUInt8, (a0 >>> 48).toUInt8, (a0 >>> 56).toUInt8, (a5 >>> 0).toUInt8, (a5 >>> 8).toUInt8,
        (a5 >>> 16).toUInt8, (a5 >>> 24).toUInt8, (a5 >>> 32).toUInt8, (a5 >>> 40).toUInt8, (a5 >>> 48).toUInt8,
        (a5 >>> 56).toUInt8, (a10 >>> 0).toUInt8, (a10 >>> 8).toUInt8, (a10 >>> 16).toUInt8, (a10 >>> 24).toUInt8,
        (a10 >>> 32).toUInt8, (a10 >>> 40).toUInt8, (a10 >>> 48).toUInt8, (a10 >>> 56).toUInt8, (a15 >>> 0).toUInt8,
        (a15 >>> 8).toUInt8, (a15 >>> 16).toUInt8, (a15 >>> 24).toUInt8, (a15 >>> 32).toUInt8, (a15 >>> 40).toUInt8,
        (a15 >>> 48).toUInt8, (a15 >>> 56).toUInt8]⟩
  := by
    unfold LeanCrypto.HashFunctions.squeeze'
    unfold LeanCrypto.HashFunctions.squeeze'.stateToBytes
    simp [
      h_bytes,
      LeanCrypto.HashFunctions.squeeze'.extract,
      ByteArray.extract',
      ByteArray.extract,
      ByteArray.empty, ByteArray.mkEmpty,
      ByteArray.copySlice, Array.extract,
      LeanCrypto.HashFunctions.squeeze'.lanesToExtract,
      Rat.ceil
    ]
    have : ((64: ℚ) / (8: ℚ )) = 8 := by
      rewrite [
        ←Nat.cast_ofNat (n := 64),
        ←Nat.cast_ofNat (n := 8),
        Rat.natCast_div_eq_divInt,
      ]
      simp
      apply (Rat.divInt_eq_iff (n₁ := 64) (d₁ := 8) (n₂ := 8) (d₂ := 1) (by trivial) (by trivial)).mpr
      decide
    have : ((32:ℚ) / ((64: ℚ) / (8: ℚ ))) = 4 := by
      rewrite [this]
      rewrite [
        ←Nat.cast_ofNat (n := 32),
        ←Nat.cast_ofNat (n := 8),
        Rat.natCast_div_eq_divInt,
      ]
      simp
      apply (Rat.divInt_eq_iff (n₁ := 32) (d₁ := 8) (n₂ := 4) (d₂ := 1) (by trivial) (by trivial)).mpr
      decide
    simp [this]
    have : @Array.extract.loop UInt8 #[] 0 0 #[] = #[] := by rfl
    simp [this]
    simp [
      LeanCrypto.HashFunctions.squeeze'.extract,
      LeanCrypto.HashFunctions.Absorb.unfoldrN,
      LeanCrypto.HashFunctions.Absorb.unfoldrN.go,
    ]
    simp [
      LeanCrypto.HashFunctions.squeeze'.toLittleEndian,
      ByteArray.empty, ByteArray.mkEmpty, ByteArray.push,
      show Array.extract.loop #[] 0 32 #[] = #[] by rfl
    ]
    simp [Array.extract.loop]

  lemma keccakF_size (h_state_size: state.size = 25):
    (LeanCrypto.HashFunctions.keccakF state).size = 25
  := by
    simp [
      LeanCrypto.HashFunctions.keccakF,
      LeanCrypto.HashFunctions.Rounds,
      Array.foldl1,
      LeanCrypto.HashFunctions.keccakF.f
    ]
    repeat (
      apply iota_size
      apply chi_size
      apply pi_size
      apply rho_size
      apply theta_size
    )
    assumption

  lemma state_array_eval :
    state_array c = #[{
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 1 79).val ++ BitVec.ofNat 8 (cell_manager c 1 78).val ++
                    BitVec.ofNat 8 (cell_manager c 1 77).val ++
                  BitVec.ofNat 8 (cell_manager c 1 76).val ++
                BitVec.ofNat 8 (cell_manager c 1 75).val ++
              BitVec.ofNat 8 (cell_manager c 1 74).val ++
            BitVec.ofNat 8 (cell_manager c 1 73).val ++
          BitVec.ofNat 8 (cell_manager c 1 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 6 79).val ++ BitVec.ofNat 8 (cell_manager c 6 78).val ++
                    BitVec.ofNat 8 (cell_manager c 6 77).val ++
                  BitVec.ofNat 8 (cell_manager c 6 76).val ++
                BitVec.ofNat 8 (cell_manager c 6 75).val ++
              BitVec.ofNat 8 (cell_manager c 6 74).val ++
            BitVec.ofNat 8 (cell_manager c 6 73).val ++
          BitVec.ofNat 8 (cell_manager c 6 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 11 79).val ++ BitVec.ofNat 8 (cell_manager c 11 78).val ++
                    BitVec.ofNat 8 (cell_manager c 11 77).val ++
                  BitVec.ofNat 8 (cell_manager c 11 76).val ++
                BitVec.ofNat 8 (cell_manager c 11 75).val ++
              BitVec.ofNat 8 (cell_manager c 11 74).val ++
            BitVec.ofNat 8 (cell_manager c 11 73).val ++
          BitVec.ofNat 8 (cell_manager c 11 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 16 79).val ++ BitVec.ofNat 8 (cell_manager c 16 78).val ++
                    BitVec.ofNat 8 (cell_manager c 16 77).val ++
                  BitVec.ofNat 8 (cell_manager c 16 76).val ++
                BitVec.ofNat 8 (cell_manager c 16 75).val ++
              BitVec.ofNat 8 (cell_manager c 16 74).val ++
            BitVec.ofNat 8 (cell_manager c 16 73).val ++
          BitVec.ofNat 8 (cell_manager c 16 72).val },
    0,
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 2 79).val ++ BitVec.ofNat 8 (cell_manager c 2 78).val ++
                    BitVec.ofNat 8 (cell_manager c 2 77).val ++
                  BitVec.ofNat 8 (cell_manager c 2 76).val ++
                BitVec.ofNat 8 (cell_manager c 2 75).val ++
              BitVec.ofNat 8 (cell_manager c 2 74).val ++
            BitVec.ofNat 8 (cell_manager c 2 73).val ++
          BitVec.ofNat 8 (cell_manager c 2 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 7 79).val ++ BitVec.ofNat 8 (cell_manager c 7 78).val ++
                    BitVec.ofNat 8 (cell_manager c 7 77).val ++
                  BitVec.ofNat 8 (cell_manager c 7 76).val ++
                BitVec.ofNat 8 (cell_manager c 7 75).val ++
              BitVec.ofNat 8 (cell_manager c 7 74).val ++
            BitVec.ofNat 8 (cell_manager c 7 73).val ++
          BitVec.ofNat 8 (cell_manager c 7 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 12 79).val ++ BitVec.ofNat 8 (cell_manager c 12 78).val ++
                    BitVec.ofNat 8 (cell_manager c 12 77).val ++
                  BitVec.ofNat 8 (cell_manager c 12 76).val ++
                BitVec.ofNat 8 (cell_manager c 12 75).val ++
              BitVec.ofNat 8 (cell_manager c 12 74).val ++
            BitVec.ofNat 8 (cell_manager c 12 73).val ++
          BitVec.ofNat 8 (cell_manager c 12 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 17 79).val ++ BitVec.ofNat 8 (cell_manager c 17 78).val ++
                    BitVec.ofNat 8 (cell_manager c 17 77).val ++
                  BitVec.ofNat 8 (cell_manager c 17 76).val ++
                BitVec.ofNat 8 (cell_manager c 17 75).val ++
              BitVec.ofNat 8 (cell_manager c 17 74).val ++
            BitVec.ofNat 8 (cell_manager c 17 73).val ++
          BitVec.ofNat 8 (cell_manager c 17 72).val },
    0,
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 3 79).val ++ BitVec.ofNat 8 (cell_manager c 3 78).val ++
                    BitVec.ofNat 8 (cell_manager c 3 77).val ++
                  BitVec.ofNat 8 (cell_manager c 3 76).val ++
                BitVec.ofNat 8 (cell_manager c 3 75).val ++
              BitVec.ofNat 8 (cell_manager c 3 74).val ++
            BitVec.ofNat 8 (cell_manager c 3 73).val ++
          BitVec.ofNat 8 (cell_manager c 3 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 8 79).val ++ BitVec.ofNat 8 (cell_manager c 8 78).val ++
                    BitVec.ofNat 8 (cell_manager c 8 77).val ++
                  BitVec.ofNat 8 (cell_manager c 8 76).val ++
                BitVec.ofNat 8 (cell_manager c 8 75).val ++
              BitVec.ofNat 8 (cell_manager c 8 74).val ++
            BitVec.ofNat 8 (cell_manager c 8 73).val ++
          BitVec.ofNat 8 (cell_manager c 8 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 13 79).val ++ BitVec.ofNat 8 (cell_manager c 13 78).val ++
                    BitVec.ofNat 8 (cell_manager c 13 77).val ++
                  BitVec.ofNat 8 (cell_manager c 13 76).val ++
                BitVec.ofNat 8 (cell_manager c 13 75).val ++
              BitVec.ofNat 8 (cell_manager c 13 74).val ++
            BitVec.ofNat 8 (cell_manager c 13 73).val ++
          BitVec.ofNat 8 (cell_manager c 13 72).val },
    0, 0,
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 4 79).val ++ BitVec.ofNat 8 (cell_manager c 4 78).val ++
                    BitVec.ofNat 8 (cell_manager c 4 77).val ++
                  BitVec.ofNat 8 (cell_manager c 4 76).val ++
                BitVec.ofNat 8 (cell_manager c 4 75).val ++
              BitVec.ofNat 8 (cell_manager c 4 74).val ++
            BitVec.ofNat 8 (cell_manager c 4 73).val ++
          BitVec.ofNat 8 (cell_manager c 4 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 9 79).val ++ BitVec.ofNat 8 (cell_manager c 9 78).val ++
                    BitVec.ofNat 8 (cell_manager c 9 77).val ++
                  BitVec.ofNat 8 (cell_manager c 9 76).val ++
                BitVec.ofNat 8 (cell_manager c 9 75).val ++
              BitVec.ofNat 8 (cell_manager c 9 74).val ++
            BitVec.ofNat 8 (cell_manager c 9 73).val ++
          BitVec.ofNat 8 (cell_manager c 9 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 14 79).val ++ BitVec.ofNat 8 (cell_manager c 14 78).val ++
                    BitVec.ofNat 8 (cell_manager c 14 77).val ++
                  BitVec.ofNat 8 (cell_manager c 14 76).val ++
                BitVec.ofNat 8 (cell_manager c 14 75).val ++
              BitVec.ofNat 8 (cell_manager c 14 74).val ++
            BitVec.ofNat 8 (cell_manager c 14 73).val ++
          BitVec.ofNat 8 (cell_manager c 14 72).val },
    0, 0,
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 5 79).val ++ BitVec.ofNat 8 (cell_manager c 5 78).val ++
                    BitVec.ofNat 8 (cell_manager c 5 77).val ++
                  BitVec.ofNat 8 (cell_manager c 5 76).val ++
                BitVec.ofNat 8 (cell_manager c 5 75).val ++
              BitVec.ofNat 8 (cell_manager c 5 74).val ++
            BitVec.ofNat 8 (cell_manager c 5 73).val ++
          BitVec.ofNat 8 (cell_manager c 5 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 10 79).val ++ BitVec.ofNat 8 (cell_manager c 10 78).val ++
                    BitVec.ofNat 8 (cell_manager c 10 77).val ++
                  BitVec.ofNat 8 (cell_manager c 10 76).val ++
                BitVec.ofNat 8 (cell_manager c 10 75).val ++
              BitVec.ofNat 8 (cell_manager c 10 74).val ++
            BitVec.ofNat 8 (cell_manager c 10 73).val ++
          BitVec.ofNat 8 (cell_manager c 10 72).val },
    {
      toBitVec :=
        BitVec.ofNat 8 (cell_manager c 15 79).val ++ BitVec.ofNat 8 (cell_manager c 15 78).val ++
                    BitVec.ofNat 8 (cell_manager c 15 77).val ++
                  BitVec.ofNat 8 (cell_manager c 15 76).val ++
                BitVec.ofNat 8 (cell_manager c 15 75).val ++
              BitVec.ofNat 8 (cell_manager c 15 74).val ++
            BitVec.ofNat 8 (cell_manager c 15 73).val ++
          BitVec.ofNat 8 (cell_manager c 15 72).val },
    0, 0]
  := by
    unfold state_array
    simp [array_range_25, state_x_y, absorb_positions, fin_vals, a_slice]

  def input_bytearray (c: ValidCircuit P P_Prime): ByteArray :=
    ⟨
      ((input_bytes_sublist c 136).map (λ x => UInt8.ofBitVec (BitVec.ofNat 8 x.val))).toArray
    ⟩

  lemma hash_bytes_eval: hash_bytes c 25 = [cell_manager c 24 1680, cell_manager c 24 1681, cell_manager c 24 1682, cell_manager c 24 1683, cell_manager c 24 1684,
    cell_manager c 24 1685, cell_manager c 24 1686, cell_manager c 24 1687, cell_manager c 23 1680,
    cell_manager c 23 1681, cell_manager c 23 1682, cell_manager c 23 1683, cell_manager c 23 1684,
    cell_manager c 23 1685, cell_manager c 23 1686, cell_manager c 23 1687, cell_manager c 22 1680,
    cell_manager c 22 1681, cell_manager c 22 1682, cell_manager c 22 1683, cell_manager c 22 1684,
    cell_manager c 22 1685, cell_manager c 22 1686, cell_manager c 22 1687, cell_manager c 21 1680,
    cell_manager c 21 1681, cell_manager c 21 1682, cell_manager c 21 1683, cell_manager c 21 1684,
    cell_manager c 21 1685, cell_manager c 21 1686, cell_manager c 21 1687] := by
    unfold hash_bytes squeeze_bytes
    simp [squeeze_from, Transform.split_expr, Split.expr_res, word_parts_known]

  def output_bytearray (c: ValidCircuit P P_Prime): ByteArray :=
    ⟨
      ((hash_bytes c 25).map (λ x => UInt8.ofBitVec (BitVec.ofNat 8 x.val))).toArray
    ⟩

  lemma hash_bytes_length: (hash_bytes c 25).length = 32 := by
    simp [hash_bytes, squeeze_bytes, Transform.split_expr, Split.expr_res, word_parts_known]

  lemma hash_bytes_value_range
    {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c)
    (h_idx: idx < 32) (h_P: P ≥ 256):
    (hash_bytes c 25)[idx].val < 256
  := by
    unfold hash_bytes
    simp
    have h_squeeze_bytes := Proofs.squeeze_bytes_of_meets_constraints h_meets_constraints
    simp [
      squeeze_bytes.eq_def, keccak_constants, Transform.split_expr, packed_parts.eq_def,
      Split.expr.eq_def, Split.constraint.eq_def, Split.expr_res.eq_def, word_parts_known,
      squeeze_from, squeeze_from_parts
    ] at h_squeeze_bytes
    simp [
      squeeze_bytes.eq_def, keccak_constants, Transform.split_expr, Split.expr_res.eq_def, word_parts_known
    ]
    by_cases idx = 0
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.1 h_P; simp_all
    by_cases idx = 1
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.1 h_P; simp_all
    by_cases idx = 2
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.2.1 h_P; simp_all
    by_cases idx = 3
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.2.2.1 h_P; simp_all
    by_cases idx = 4
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 5
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 6
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 7
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 24 (by trivial) (by trivial)).2.2.2.2.2.2.2.2 h_P; simp_all
    by_cases idx = 8
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.1 h_P; simp_all
    by_cases idx = 9
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.1 h_P; simp_all
    by_cases idx = 10
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.2.1 h_P; simp_all
    by_cases idx = 11
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.2.2.1 h_P; simp_all
    by_cases idx = 12
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 13
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 14
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 15
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 23 (by trivial) (by trivial)).2.2.2.2.2.2.2.2 h_P; simp_all
    by_cases idx = 16
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.1 h_P; simp_all
    by_cases idx = 17
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.1 h_P; simp_all
    by_cases idx = 18
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.2.1 h_P; simp_all
    by_cases idx = 19
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.2.2.1 h_P; simp_all
    by_cases idx = 20
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 21
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 22
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 23
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 22 (by trivial) (by trivial)).2.2.2.2.2.2.2.2 h_P; simp_all
    by_cases idx = 24
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.1 h_P; simp_all
    by_cases idx = 25
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.1 h_P; simp_all
    by_cases idx = 26
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.2.1 h_P; simp_all
    by_cases idx = 27
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.2.2.1 h_P; simp_all
    by_cases idx = 28
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 29
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 30
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 31
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ (h_squeeze_bytes 21 (by trivial) (by trivial)).2.2.2.2.2.2.2.2 h_P; simp_all
    omega

  lemma squeeze_absorb_eval {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c) (h_P: P ≥ 2^200)
    (h_is_paddings: is_paddings c 17 (-1) = 1):
    LeanCrypto.HashFunctions.squeeze' 1088 h 32 (
      LeanCrypto.HashFunctions.Absorb.absorb
        1088
        (by trivial)
        (LeanCrypto.HashFunctions.byteArrayOfSHA3SR
          (LeanCrypto.HashFunctions.SHA3SRofByteArray (input_bytearray c))
        )
    ) = output_bytearray c
  := by
    unfold input_bytearray
    rewrite [input_bytes_sublist_eq_calc]
    unfold input_bytes_sublist_calc
    simp only [List.take_succ_cons, List.take_nil, List.map_cons, List.map_nil]
    rewrite [absorb_bytes_with_conversion_eval _ (by trivial)]
    . generalize h_post_state :LeanCrypto.HashFunctions.keccakF _ = post_state
      have : post_state.size = 25 := by simp [←h_post_state, keccakF_size]
      have := array_ext_25 this
      rewrite [squeeze_eval this]
      have h_state: post_state = LeanCrypto.HashFunctions.keccakF (state_array c) := by
        rewrite [←h_post_state]
        clear h_post_state
        rewrite [state_array_eval]
        simp [input_bytes, keccak_constants, -UInt8.ofBitVec_ofNat, Transform.split_expr, Split.expr_res]
        have (x: ZMod P) :
          ({ toBitVec := BitVec.ofNat 8 x.val }: UInt8).toUInt64 =
          UInt64.ofBitVec (BitVec.setWidth 64 (BitVec.ofNat 8 x.val))
        := by
          rw [UInt64.ofBitVec_uInt8ToBitVec]
        simp only [this]
        have (bv: BitVec 64) (n: ℕ):
          (UInt64.ofBitVec bv) <<< UInt64.ofNat n = UInt64.ofBitVec (bv <<< (n % 64))
        := by
          apply UInt64.eq_of_toBitVec_eq
          simp
        have (bv) := this bv 0
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 8
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 16
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 24
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 32
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 40
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 48
        simp at this
        simp [this]
        clear this
        have (bv) := this bv 56
        simp at this
        simp [this]
        clear this
        have (bv1 bv2: BitVec 64) :
          UInt64.ofBitVec bv1 ^^^ UInt64.ofBitVec bv2 = UInt64.ofBitVec (bv1 ^^^ bv2)
        := by
          apply UInt64.eq_of_toBitVec_eq
          simp
        simp only [this]
        have (x0 x1 x2 x3 x4 x5 x6 x7: ZMod P):
          BitVec.setWidth 64 (BitVec.ofNat 8 x0.val) ^^^
                        BitVec.setWidth 64 (BitVec.ofNat 8 x1.val) <<< 8 ^^^
                      BitVec.setWidth 64 (BitVec.ofNat 8 x2.val) <<< 16 ^^^
                    BitVec.setWidth 64 (BitVec.ofNat 8 x3.val) <<< 24 ^^^
                  BitVec.setWidth 64 (BitVec.ofNat 8 x4.val) <<< 32 ^^^
                BitVec.setWidth 64 (BitVec.ofNat 8 x5.val) <<< 40 ^^^
              BitVec.setWidth 64 (BitVec.ofNat 8 x6.val) <<< 48 ^^^
            BitVec.setWidth 64 (BitVec.ofNat 8 x7.val) <<< 56 =
          BitVec.ofNat 8 x7.val ++ BitVec.ofNat 8 x6.val ++
                      BitVec.ofNat 8 x5.val ++
                    BitVec.ofNat 8 x4.val ++
                  BitVec.ofNat 8 x3.val ++
                BitVec.ofNat 8 x2.val ++
              BitVec.ofNat 8 x1.val ++
            BitVec.ofNat 8 x0.val
        := by
          bv_decide
        simp [this]
      simp [h_state]
      clear h_post_state this
      simp [←UInt8.ofBitVec_uInt64ToBitVec]
      have h_output := output_spec_of_padding h_meets_constraints (y := 0) h_P (by trivial) h_is_paddings
      simp [fin_vals, Array.getElem?_eq_some_iff] at h_output
      obtain ⟨_, h_output⟩ := h_output
      rewrite [h_output]
      have h_output := output_spec_of_padding h_meets_constraints (y := 1) h_P (by trivial) h_is_paddings
      simp [fin_vals, Array.getElem?_eq_some_iff] at h_output
      obtain ⟨_, h_output⟩ := h_output
      rewrite [h_output]
      have h_output := output_spec_of_padding h_meets_constraints (y := 2) h_P (by trivial) h_is_paddings
      simp [fin_vals, Array.getElem?_eq_some_iff] at h_output
      obtain ⟨_, h_output⟩ := h_output
      rewrite [h_output]
      have h_output := output_spec_of_padding h_meets_constraints (y := 3) h_P (by trivial) h_is_paddings
      simp [fin_vals, Array.getElem?_eq_some_iff] at h_output
      obtain ⟨_, h_output⟩ := h_output
      rewrite [h_output]
      unfold output_bytearray
      rewrite [hash_bytes_eval]
      simp [-UInt8.ofBitVec_ofNat]
      bv_decide
    . trivial







    --   LeanCrypto.HashFunctions.Absorb.toBlocks.toLane,
    --   LeanCrypto.HashFunctions.Absorb.unfoldr,
    --   LeanCrypto.HashFunctions.Absorb.ifoldl,
    --   LeanCrypto.HashFunctions.Absorb.toBlocks.createWord64
    -- ]
    -- unfold LeanCrypto.HashFunctions.Absorb.absorb
    -- unfold LeanCrypto.HashFunctions.Absorb.toBlocks
    -- unfold LeanCrypto.HashFunctions.Absorb.toBlocks.toLane
    -- simp
    -- unfold LeanCrypto.HashFunctions.Absorb.ifoldl
    -- unfold LeanCrypto.HashFunctions.Absorb.toBlocks.createWord64

  -- #eval LeanCrypto.HashFunctions.Absorb.absorb 1088 ⟨#[
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5,6,7,8,9,
  --   0,1,2,3,4,5
  -- ]⟩

  -- lemma absorb_spec {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: P ≥ 2^200) (h_y: y < 4) (h_is_paddings: is_paddings c 17 (-1) = 1):
  --   (LeanCrypto.HashFunctions.Absorb.absorb 1088 (state_bytes c)) =
  --   (LeanCrypto.HashFunctions.keccakF (state_array c))
  -- := by
  --   unfold LeanCrypto.HashFunctions.Absorb.absorb
  --   have (rate) (state) (input) :
  --     LeanCrypto.HashFunctions.Absorb.absorbBlock rate state input =
  --     if input.size == 0 then state
  --     else LeanCrypto.HashFunctions.Absorb.absorbBlock rate (LeanCrypto.HashFunctions.keccakF (Array.mapIdx (λ z el ↦ if z / 5 + 5 * (z % 5) < rate / 64
  --                                                 then el ^^^ (input[z / 5 + 5 * (z % 5)]!)
  --                                                 else el) state)) (input.drop (rate / 64))
  --   := by
  --     rewrite [LeanCrypto.HashFunctions.Absorb.absorbBlock]
  --   rewrite [LeanCrypto.HashFunctions.Absorb.absorbBlock.eq_def]
  --   done
end Keccak.Soundness

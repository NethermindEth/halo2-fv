import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  def bit_invert (x width: ℕ) := (~~~(BitVec.ofNat (width*BIT_COUNT) x)).toNat

  lemma bit_invert_lt (x width: ℕ): bit_invert x width < 2^(width*3) := by
    simp [bit_invert.eq_def, keccak_constants]
    omega

  lemma bit_invert_4_lt (x: ℕ): bit_invert x 4 < 4096 := by
    convert bit_invert_lt x 4

  lemma bit_invert_normalized_eq_xor (h: x = Normalize.normalize_unpacked x' 4):
    bit_invert x 4 = 4095 ^^^ x
  := by
    simp only [
      h,
      bit_invert.eq_def,
    ]
    rewrite [show 4095 = (4095#192).toNat by decide]
    simp only [
      Normalize.normalize_unpacked_to_bitvec,
      ←BitVec.toNat_xor,
      keccak_constants, Nat.reduceMul,
    ]
    rewrite [BitVec.ofNat_toNat]
    have : (BitVec.setWidth 192 (
        ~~~BitVec.setWidth 12 (
          BitVec.ofNat 192 x' &&&
          BitVec.ofNat 192 Normalize.mask &&&
          BitVec.setWidth 192 (BitVec.allOnes 12))
      )) = (
        4095#192 ^^^
        BitVec.ofNat 192 x' &&&
        BitVec.ofNat 192 Normalize.mask &&& BitVec.setWidth 192 (BitVec.allOnes 12)
      )
    := by
      simp only [Normalize.mask_bitvec_ofNat, Normalize.mask_bitvec.eq_def]
      bv_decide
    rewrite [←this]
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    bv_omega

  lemma bit_invert_to_bitvec:
    (BitVec.ofNat (width*BIT_COUNT) (bit_invert x width)).toNat =
    bit_invert x width
  := by
    simp [
      bit_invert.eq_def, keccak_constants
    ]
    rw [Nat.mod_eq_of_lt (a := _ - _ - _) (by omega)]

  lemma normalize_bit_invert_normalize_4:
    Normalize.normalize_unpacked (
      bit_invert (
        Normalize.normalize_unpacked x 4
      ) 4
    ) 4 =
    Normalize.normalize_unpacked (bit_invert x 4) 4
  := by
    simp only [
      Normalize.normalize_unpacked.eq_def,
      bit_invert.eq_def,
      keccak_constants,
      Nat.reduceMul
    ]
    simp [←Nat.and_pow_two_sub_one_eq_mod _ 12, Nat.and_assoc, Normalize.mask]
    have : (x &&& 585) = (x &&& 4095 &&& 585) := by simp [Nat.and_assoc]
    rewrite [this]
    have : (x &&& 4095) = (BitVec.ofNat 12 x).toNat := by simp [Nat.and_pow_two_sub_one_eq_mod _ 12]
    rewrite [
      this,
      show 4095 = (4095#12).toNat by decide,
      show 585 = (585#12).toNat by decide,
      ←BitVec.toNat_and,
      ←BitVec.toNat_sub_of_le,
      ←BitVec.toNat_sub_of_le,
      ←BitVec.toNat_and,
      ←BitVec.toNat_and,
      ←BitVec.toNat_eq
    ]
    . bv_decide
    . simp; omega
    . bv_omega

  lemma normalize_bit_invert_normalize_64:
    Normalize.normalize_unpacked (
      bit_invert (
        Normalize.normalize_unpacked x 64
      ) 64
    ) 64 =
    Normalize.normalize_unpacked (bit_invert x 64) 64
  := by
    simp only [
      Normalize.normalize_unpacked.eq_def,
      bit_invert.eq_def,
      keccak_constants,
      ←Normalize.mask_bitvec_toNat,
      Nat.reduceMul
    ]
    have : 8 ^ 64 - 1 = (BitVec.allOnes 192).toNat := by decide
    rewrite [this]
    simp only [←BitVec.toNat_and]
    congr 1
    have (x) : BitVec.ofNat 192 (x &&& (BitVec.allOnes 192).toNat) = BitVec.ofNat 192 x := by
      apply BitVec.toNat_eq.mpr
      simp
      rewrite [Nat.and_pow_two_sub_one_eq_mod x 192]
      rw [Nat.mod_mod]
    rewrite [this]
    rewrite [BitVec.and_assoc, BitVec.and_assoc, BitVec.and_allOnes]
    have : (BitVec.ofNat 192 x) &&& Normalize.mask_bitvec = BitVec.ofNat 192 (x &&& Normalize.mask_bitvec.toNat) := by
      apply BitVec.toNat_eq.mpr
      rw [
        BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        ←Nat.and_pow_two_sub_one_eq_mod,
        ←Nat.and_pow_two_sub_one_eq_mod,
        Nat.and_assoc,
        Nat.and_comm (2^_ - _),
        ←Nat.and_assoc
      ]
    rewrite [←this]
    bv_decide


  lemma bit_invert_4_shift_12_add (h_y: y < 2^12) :
    bit_invert x 4 <<< 12 +
    bit_invert y 4 =
    bit_invert (x <<< 12 + y) 8
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_24_add (h_y: y < 2^24) :
    bit_invert x 4 <<< 24 +
    bit_invert y 8 =
    bit_invert (x <<< 24 + y) 12
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_36_add (h_y: y < 2^36) :
    bit_invert x 4 <<< 36 +
    bit_invert y 12 =
    bit_invert (x <<< 36 + y) 16
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_48_add (h_y: y < 2^48) :
    bit_invert x 4 <<< 48 +
    bit_invert y 16 =
    bit_invert (x <<< 48 + y) 20
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_60_add (h_y: y < 2^60) :
    bit_invert x 4 <<< 60 +
    bit_invert y 20 =
    bit_invert (x <<< 60 + y) 24
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_72_add (h_y: y < 2^72) :
    bit_invert x 4 <<< 72 +
    bit_invert y 24 =
    bit_invert (x <<< 72 + y) 28
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_84_add (h_y: y < 2^84) :
    bit_invert x 4 <<< 84 +
    bit_invert y 28 =
    bit_invert (x <<< 84 + y) 32
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_96_add (h_y: y < 2^96) :
    bit_invert x 4 <<< 96 +
    bit_invert y 32 =
    bit_invert (x <<< 96 + y) 36
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_108_add (h_y: y < 2^108) :
    bit_invert x 4 <<< 108 +
    bit_invert y 36 =
    bit_invert (x <<< 108 + y) 40
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_120_add (h_y: y < 2^120) :
    bit_invert x 4 <<< 120 +
    bit_invert y 40 =
    bit_invert (x <<< 120 + y) 44
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_132_add (h_y: y < 2^132) :
    bit_invert x 4 <<< 132 +
    bit_invert y 44 =
    bit_invert (x <<< 132 + y) 48
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_144_add (h_y: y < 2^144) :
    bit_invert x 4 <<< 144 +
    bit_invert y 48 =
    bit_invert (x <<< 144 + y) 52
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_156_add (h_y: y < 2^156) :
    bit_invert x 4 <<< 156 +
    bit_invert y 52 =
    bit_invert (x <<< 156 + y) 56
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_168_add (h_y: y < 2^168) :
    bit_invert x 4 <<< 168 +
    bit_invert y 56 =
    bit_invert (x <<< 168 + y) 60
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

  lemma bit_invert_4_shift_180_add (h_y: y < 2^180) :
    bit_invert x 4 <<< 180 +
    bit_invert y 60 =
    bit_invert (x <<< 180 + y) 64
  := by
    simp [
      bit_invert.eq_def,
      keccak_constants,
      Nat.shiftLeft_eq,
      Nat.sub_mul
    ]
    omega

end Keccak.Soundness

import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness

  namespace Normalize

  def mask := 0b001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001
  def mask_3 := 0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001001001001001001
  def mask_4 := 0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001001001001
  def mask_6 := 0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001001001
  def mask_bitvec := 0b001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001#192
  def mask_3_bitvec := 0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001001001001001001#192
  def mask_4_bitvec := 0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001001001001#192
  def mask_6_bitvec := 0b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001001001#192
  lemma mask_lt: mask < BIT_SIZE^64 := by
    simp [keccak_constants]
    decide
  lemma mask_gt: mask > BIT_SIZE^63:= by
    simp [keccak_constants]
    decide
  lemma mask_3_lt: mask_3 < BIT_SIZE^6 := by
    simp [keccak_constants]
    decide
  lemma mask_3_gt: mask_3 > BIT_SIZE^5:= by
    simp [keccak_constants]
    decide
  lemma mask_4_lt: mask_4 < BIT_SIZE^4 := by
    simp [keccak_constants]
    decide
  lemma mask_4_gt: mask_4 > BIT_SIZE^3:= by
    simp [keccak_constants]
    decide
  lemma mask_6_lt: mask_6 < BIT_SIZE^3 := by
    simp [keccak_constants]
    decide
  lemma mask_6_gt: mask_6 > BIT_SIZE^2:= by
    simp [keccak_constants]
    decide
  lemma mask_mod_2_pow_192: mask % (2^192) = mask := by decide
  lemma mask_and_2_pow_192_sub_one: mask &&& (2^192 - 1) = mask := by decide
  lemma mask_and_2_pow_192_sub_one': (2^192 - 1) &&& mask = mask := by decide
  lemma mask_bitvec_ofNat: BitVec.ofNat 192 mask = mask_bitvec := by decide
  lemma mask_bitvec_toNat: BitVec.toNat mask_bitvec = mask := by decide

  def normalize_unpacked (x bits: ℕ) := x &&& mask &&& (BIT_SIZE^bits - 1)

  lemma normalize_unpacked_64: normalize_unpacked x 64 = x &&& mask := by
    unfold normalize_unpacked
    rewrite [Nat.and_assoc]
    simp [keccak_constants]
    congr

  lemma normalize_unpacked_64_le_mask : normalize_unpacked x 64 ≤ mask := by
    simp [normalize_unpacked.eq_def, keccak_constants, mask.eq_def, Nat.and_assoc, Nat.and_le_right]

  lemma normalize_unpacked_1_le : normalize_unpacked x 1 ≤ 1 := by
    simp [
      normalize_unpacked.eq_def,
      keccak_constants,
      Nat.and_assoc,
      mask.eq_def,
      Nat.and_le_right
    ]
    omega

  lemma normalize_unpacked_3_le : normalize_unpacked x 3 ≤ 73 := by
    simp [
      normalize_unpacked.eq_def,
      keccak_constants,
      Nat.and_assoc,
      mask.eq_def,
      Nat.and_le_right
    ]

  lemma normalize_unpacked_4_le : normalize_unpacked x 4 ≤ 585 := by
    simp [
      normalize_unpacked.eq_def,
      keccak_constants,
      Nat.and_assoc,
      mask.eq_def,
      Nat.and_le_right
    ]

  lemma normalize_unpacked_lt_two_pow : normalize_unpacked x bits < 2^(bits*BIT_COUNT) := by
    simp [normalize_unpacked.eq_def, keccak_constants, mul_comm bits]
    apply Nat.and_lt_two_pow
    simp [pow_mul]

  lemma normalize_unpacked_to_bitvec (x bits: Nat) : normalize_unpacked x bits = ((BitVec.ofNat 192 x) &&& (BitVec.ofNat 192 mask) &&& BitVec.setWidth 192 (BitVec.allOnes (BIT_COUNT*bits))).toNat := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, mask_mod_2_pow_192]
    unfold normalize_unpacked
    simp only [←Nat.and_pow_two_sub_one_eq_mod, Nat.and_assoc]
    congr 1
    simp only [←Nat.and_assoc]
    rewrite (occs := .pos [1]) [←mask_and_2_pow_192_sub_one]
    rewrite [Nat.and_comm _ mask]
    simp only [Nat.and_assoc]
    congr 1
    unfold BitVec.setWidth
    by_cases h: BIT_COUNT * bits ≤ 192
    . rewrite [dite_cond_eq_true (by simp_all)]
      simp only [BIT_SIZE.eq_def, ←BitVec.toNat_allOnes, ←pow_mul]
      congr 1
    . rewrite [dite_cond_eq_false (by simp_all)]
      simp at h
      unfold BitVec.ofNat Fin.ofNat'
      simp only [allOnes_toNat_mod_2pow h]
      simp only [BIT_SIZE.eq_def, ←Nat.pow_mul]
      rewrite [Nat.and_pow_two_sub_one_of_lt_two_pow]
      simp
      have : 2 ^ 192 < 2 ^ (BIT_COUNT * bits) := Nat.pow_lt_pow_right (by trivial) (by assumption)
      omega

  lemma normalize_unpacked_ofNat_toNat (h: k = BIT_COUNT*bits):
    normalize_unpacked (BitVec.ofNat k x).toNat bits =
    normalize_unpacked x bits
  := by
    simp_all [
      keccak_constants,
      normalize_unpacked.eq_def,
      ←Nat.and_pow_two_sub_one_eq_mod,
    ]
    simp [pow_mul]
    rw [
      Nat.and_assoc x, Nat.and_comm _ mask, ←Nat.and_assoc,
      Nat.and_assoc, Nat.and_self
    ]

  lemma normalize_unpacked_idempotent :
    normalize_unpacked (normalize_unpacked x k) k = normalize_unpacked x k
  := by
    simp only [
      normalize_unpacked_to_bitvec, keccak_constants,
      BitVec.ofNat_toNat
    ]
    congr 1
    bv_decide

  lemma normalize_unpacked_toNat {b: BitVec 192} :
    normalize_unpacked (b.toNat) bits = (b &&& mask_bitvec &&& BitVec.setWidth 192 (BitVec.allOnes (BIT_COUNT*bits))).toNat
  := by
    simp [normalize_unpacked_to_bitvec, mask_bitvec_ofNat]

  lemma normalize_unpacked_toNat_small {b: BitVec n} (h: n < 192):
    normalize_unpacked (b.toNat) bits = (BitVec.setWidth 192 b &&& mask_bitvec &&& BitVec.setWidth 192 (BitVec.allOnes (BIT_COUNT*bits))).toNat
  := by
    rewrite [←normalize_unpacked_toNat]
    congr 1
    simp
    rw [Nat.mod_eq_of_lt]
    exact lt_trans
      (show b.toNat < 2^n by bv_omega)
      (show 2^n < 2^192 by exact Nat.pow_lt_pow_right (by trivial) (by assumption))

  lemma normalize_shrink_6_4:
    Normalize.normalize_unpacked (BitVec.ofNat 12 n).toNat 6 =
    Normalize.normalize_unpacked (BitVec.ofNat 12 n).toNat 4
  := by
    rewrite [
      normalize_unpacked_toNat_small,
      normalize_unpacked_toNat_small
    ]
    . simp only [keccak_constants, mask_bitvec.eq_def, Nat.reduceMul]
      congr 1
      bv_decide
    all_goals trivial

  lemma self_normalize_of_normalized_4 [NeZero P] (x: ZMod P) (h_P: 585 < P) (h_x: x.val = Normalize.normalize_unpacked x' 4):
    x = Normalize.normalize_unpacked x.val 4
  := by
      apply ZMod.val_injective
      simp [h_x]
      rw [
        Normalize.normalize_unpacked_idempotent,
        Nat.mod_eq_of_lt
      ]
      exact lt_of_le_of_lt
        Normalize.normalize_unpacked_4_le
        h_P

    lemma normalize_3_shift_3_add {bv1: BitVec 9} {bv2: BitVec 3} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 3 +
    Normalize.normalize_unpacked bv2.toNat 1 =
    Normalize.normalize_unpacked (bv1.toNat <<< 3 + bv2.toNat) 4
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 3 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 584 = (584#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 1 = (1#3).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 3 &&& 584#192)
      (BitVec.setWidth 192 (bv2 &&& 1#3))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 1#3) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 3 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 3).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 3 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 585 = (585#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp [-Nat.and_one_is_mod]
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)


  lemma normalize_3_shift_9_add {bv1: BitVec 9} {bv2: BitVec 9} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 9 +
    Normalize.normalize_unpacked bv2.toNat 3 =
    Normalize.normalize_unpacked (bv1.toNat <<< 9 + bv2.toNat) 6
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 9 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 37376 = (37376#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 73 = (73#9).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 9 &&& 37376#192)
      (BitVec.setWidth 192 (bv2 &&& 73#9))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 73#9) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 9 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 9).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 9 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 37449 = (37449#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 37376) (d := 73)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_12_add {bv1: BitVec 9} {bv2: BitVec 12} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 12 +
    Normalize.normalize_unpacked bv2.toNat 4 =
    Normalize.normalize_unpacked (bv1.toNat <<< 12 + bv2.toNat) 7
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 12 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 299008 = (299008#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 585 = (585#12).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 12 &&& 299008#192)
      (BitVec.setWidth 192 (bv2 &&& 585#12))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 585#12) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 12 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 12).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 12 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 299593 = (299593#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_12_add {bv1 bv2: BitVec 12} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 12 +
    Normalize.normalize_unpacked bv2.toNat 4 =
    Normalize.normalize_unpacked (bv1.toNat <<< 12 + bv2.toNat) 8
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 12 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 2396160 = (2396160#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 585 = (585#12).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 12 &&& 2396160#192)
      (BitVec.setWidth 192 (bv2 &&& 585#12))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 585#12) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 12 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 12).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 12 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 2396745 = (2396745#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 2396160) (d := 585)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_18_add {bv1: BitVec 9} {bv2: BitVec 18} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 18 +
    Normalize.normalize_unpacked bv2.toNat 6 =
    Normalize.normalize_unpacked (bv1.toNat <<< 18 + bv2.toNat) 9
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 18 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 19136512 = (19136512#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 37449 = (37449#18).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 18 &&& 19136512#192)
      (BitVec.setWidth 192 (bv2 &&& 37449#18))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 37449#18) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 18 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 18).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 18 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 19173961 = (19173961#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 19136512) (d := 37449)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_18_add {bv1 bv2: BitVec 18} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 18 +
    Normalize.normalize_unpacked bv2.toNat 6 =
    Normalize.normalize_unpacked (bv1.toNat <<< 18 + bv2.toNat) 12
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 18 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 9817030656 = (9817030656#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 37449 = (37449#18).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 18 &&& 9817030656#192)
      (BitVec.setWidth 192 (bv2 &&& 37449#18))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 37449#18) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 18 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 18).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 18 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 9817068105 = (9817068105#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 9817030656) (d := 37449)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_21_add {bv1: BitVec 9} {bv2: BitVec 21} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 21 +
    Normalize.normalize_unpacked bv2.toNat 7 =
    Normalize.normalize_unpacked (bv1.toNat <<< 21 + bv2.toNat) 10
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 21 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 153092096 = (153092096#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 299593 = (299593#21).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 21 &&& 153092096#192)
      (BitVec.setWidth 192 (bv2 &&& 299593#21))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 299593#21) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 21 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 21).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 21 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 153391689 = (153391689#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_24_add {bv1: BitVec 12} {bv2: BitVec 24} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 24 +
    Normalize.normalize_unpacked bv2.toNat 8 =
    Normalize.normalize_unpacked (bv1.toNat <<< 24 + bv2.toNat) 12
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 24 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 9814671360 = (9814671360#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 2396745 = (2396745#24).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 24 &&& 9814671360#192)
      (BitVec.setWidth 192 (bv2 &&& 2396745#24))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 2396745#24) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 24 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 24).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 24 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 9817068105 = (9817068105#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 9814671360) (d := 2396745)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_27_add {bv1: BitVec 9} {bv2: BitVec 27} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 27 +
    Normalize.normalize_unpacked bv2.toNat 9 =
    Normalize.normalize_unpacked (bv1.toNat <<< 27 + bv2.toNat) 12
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 27 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 9797894144 = (9797894144#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 19173961 = (19173961#27).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 27 &&& 9797894144#192)
      (BitVec.setWidth 192 (bv2 &&& 19173961#27))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 19173961#27) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 27 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 27).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 27 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 9817068105 = (9817068105#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 9797894144) (d := 19173961)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_30_add {bv1: BitVec 9} {bv2: BitVec 30} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 30 +
    Normalize.normalize_unpacked bv2.toNat 10 =
    Normalize.normalize_unpacked (bv1.toNat <<< 30 + bv2.toNat) 13
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 30 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 78383153152 = (78383153152#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 153391689 = (153391689#30).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 30 &&& 78383153152#192)
      (BitVec.setWidth 192 (bv2 &&& 153391689#30))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 153391689#30) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 30 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 30).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 30 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 78536544841 = (78536544841#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_36_add {bv1: BitVec 9} {bv2: BitVec 36} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 36 +
    Normalize.normalize_unpacked bv2.toNat 12 =
    Normalize.normalize_unpacked (bv1.toNat <<< 36 + bv2.toNat) 15
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 36 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 5016521801728 = (5016521801728#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 9817068105 = (9817068105#36).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 36 &&& 5016521801728#192)
      (BitVec.setWidth 192 (bv2 &&& 9817068105#36))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 9817068105#36) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 36 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 36).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 36 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 5026338869833 = (5026338869833#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 5016521801728) (d := 9817068105)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_4_shift_36_add {bv1: BitVec 12} {bv2: BitVec 36} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 36 +
    Normalize.normalize_unpacked bv2.toNat 12 =
    Normalize.normalize_unpacked (bv1.toNat <<< 36 + bv2.toNat) 16
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 36 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 40200893890560 = (40200893890560#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 9817068105 = (9817068105#36).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 36 &&& 40200893890560#192)
      (BitVec.setWidth 192 (bv2 &&& 9817068105#36))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 9817068105#36) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 36 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 36).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 36 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 40210710958665 = (40210710958665#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 40200893890560) (d := 9817068105)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_36_add {bv1: BitVec 18} {bv2: BitVec 36} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 36 +
    Normalize.normalize_unpacked bv2.toNat 12 =
    Normalize.normalize_unpacked (bv1.toNat <<< 36 + bv2.toNat) 18
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 36 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 2573475684286464 = (2573475684286464#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 9817068105 = (9817068105#36).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 36 &&& 2573475684286464#192)
      (BitVec.setWidth 192 (bv2 &&& 9817068105#36))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 9817068105#36) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 36 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 36).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 36 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 2573485501354569 = (2573485501354569#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 2573475684286464) (d := 9817068105)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_39_add {bv1: BitVec 9} {bv2: BitVec 39} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 39 +
    Normalize.normalize_unpacked bv2.toNat 13 =
    Normalize.normalize_unpacked (bv1.toNat <<< 39 + bv2.toNat) 16
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 39 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 40132174413824 = (40132174413824#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 78536544841 = (78536544841#39).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 39 &&& 40132174413824#192)
      (BitVec.setWidth 192 (bv2 &&& 78536544841#39))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 78536544841#39) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 39 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 39).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 39 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 40210710958665 = (40210710958665#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_45_add {bv1: BitVec 9} {bv2: BitVec 45} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 45 +
    Normalize.normalize_unpacked bv2.toNat 15 =
    Normalize.normalize_unpacked (bv1.toNat <<< 45 + bv2.toNat) 18
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 45 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 2568459162484736 = (2568459162484736#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 5026338869833 = (5026338869833#45).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 45 &&& 2568459162484736#192)
      (BitVec.setWidth 192 (bv2 &&& 5026338869833#45))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 5026338869833#45) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 45 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 45).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 45 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 2573485501354569 = (2573485501354569#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 2568459162484736) (d := 5026338869833)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_48_add {bv1: BitVec 9} {bv2: BitVec 48} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 48 +
    Normalize.normalize_unpacked bv2.toNat 16 =
    Normalize.normalize_unpacked (bv1.toNat <<< 48 + bv2.toNat) 19
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 48 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 20547673299877888 = (20547673299877888#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 40210710958665 = (40210710958665#48).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 48 &&& 20547673299877888#192)
      (BitVec.setWidth 192 (bv2 &&& 40210710958665#48))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 40210710958665#48) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 48 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 48).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 48 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 20587884010836553 = (20587884010836553#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_48_add {bv1: BitVec 12} {bv2: BitVec 48} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 48 +
    Normalize.normalize_unpacked bv2.toNat 16 =
    Normalize.normalize_unpacked (bv1.toNat <<< 48 + bv2.toNat) 20
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 48 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 164662861375733760 = (164662861375733760#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 40210710958665 = (40210710958665#48).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 48 &&& 164662861375733760#192)
      (BitVec.setWidth 192 (bv2 &&& 40210710958665#48))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 40210710958665#48) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 48 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 48).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 48 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 164703072086692425 = (164703072086692425#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 164662861375733760) (d := 40210710958665)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_54_add {bv1: BitVec 9} {bv2: BitVec 54} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 54 +
    Normalize.normalize_unpacked bv2.toNat 18 =
    Normalize.normalize_unpacked (bv1.toNat <<< 54 + bv2.toNat) 21
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 54 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 1315051091192184832 = (1315051091192184832#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 2573485501354569 = (2573485501354569#54).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 54 &&& 1315051091192184832#192)
      (BitVec.setWidth 192 (bv2 &&& 2573485501354569#54))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 2573485501354569#54) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 54 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 54).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 54 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 1317624576693539401 = (1317624576693539401#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 1315051091192184832) (d := 2573485501354569)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_54_add {bv1: BitVec 18} {bv2: BitVec 54} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 54 +
    Normalize.normalize_unpacked bv2.toNat 18 =
    Normalize.normalize_unpacked (bv1.toNat <<< 54 + bv2.toNat) 24
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 54 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 674621209781590818816 = (674621209781590818816#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 2573485501354569 = (2573485501354569#54).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 54 &&& 674621209781590818816#192)
      (BitVec.setWidth 192 (bv2 &&& 2573485501354569#54))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 2573485501354569#54) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 54 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 54).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 54 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 674623783267092173385 = (674623783267092173385#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 674621209781590818816) (d := 2573485501354569)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_57_add {bv1: BitVec 9} {bv2: BitVec 57} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 57 +
    Normalize.normalize_unpacked bv2.toNat 19 =
    Normalize.normalize_unpacked (bv1.toNat <<< 57 + bv2.toNat) 22
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 57 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 10520408729537478656 = (10520408729537478656#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 20587884010836553 = (20587884010836553#57).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 57 &&& 10520408729537478656#192)
      (BitVec.setWidth 192 (bv2 &&& 20587884010836553#57))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 20587884010836553#57) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 57 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 57).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 57 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 10540996613548315209 = (10540996613548315209#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_60_add {bv1: BitVec 12} {bv2: BitVec 60} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 60 +
    Normalize.normalize_unpacked bv2.toNat 20 =
    Normalize.normalize_unpacked (bv1.toNat <<< 60 + bv2.toNat) 24
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 60 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 674459080195005480960 = (674459080195005480960#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 164703072086692425 = (164703072086692425#60).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 60 &&& 674459080195005480960#192)
      (BitVec.setWidth 192 (bv2 &&& 164703072086692425#60))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 164703072086692425#60) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 60 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 60).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 60 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 674623783267092173385 = (674623783267092173385#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 674459080195005480960) (d := 164703072086692425)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_63_add {bv1: BitVec 9} {bv2: BitVec 63} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 63 +
    Normalize.normalize_unpacked bv2.toNat 21 =
    Normalize.normalize_unpacked (bv1.toNat <<< 63 + bv2.toNat) 24
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 63 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 673306158690398633984 = (673306158690398633984#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 1317624576693539401 = (1317624576693539401#63).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 63 &&& 673306158690398633984#192)
      (BitVec.setWidth 192 (bv2 &&& 1317624576693539401#63))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 1317624576693539401#63) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 63 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 63).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 63 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 674623783267092173385 = (674623783267092173385#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_66_add {bv1: BitVec 9} {bv2: BitVec 66} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 66 +
    Normalize.normalize_unpacked bv2.toNat 22 =
    Normalize.normalize_unpacked (bv1.toNat <<< 66 + bv2.toNat) 25
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 66 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 5386449269523189071872 = (5386449269523189071872#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 10540996613548315209 = (10540996613548315209#66).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 66 &&& 5386449269523189071872#192)
      (BitVec.setWidth 192 (bv2 &&& 10540996613548315209#66))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 10540996613548315209#66) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 66 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 66).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 66 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 5396990266136737387081 = (5396990266136737387081#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_72_add {bv1: BitVec 9} {bv2: BitVec 72} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 72 +
    Normalize.normalize_unpacked bv2.toNat 24 =
    Normalize.normalize_unpacked (bv1.toNat <<< 72 + bv2.toNat) 27
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 72 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 344732753249484100599808 = (344732753249484100599808#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 674623783267092173385 = (674623783267092173385#72).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 72 &&& 344732753249484100599808#192)
      (BitVec.setWidth 192 (bv2 &&& 674623783267092173385#72))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 674623783267092173385#72) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 72 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 72).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 72 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 345407377032751192773193 = (345407377032751192773193#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_72_add {bv1: BitVec 12} {bv2: BitVec 72} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 72 +
    Normalize.normalize_unpacked bv2.toNat 24 =
    Normalize.normalize_unpacked (bv1.toNat <<< 72 + bv2.toNat) 28
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 72 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 2762584392478742450012160 = (2762584392478742450012160#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 674623783267092173385 = (674623783267092173385#72).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 72 &&& 2762584392478742450012160#192)
      (BitVec.setWidth 192 (bv2 &&& 674623783267092173385#72))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 674623783267092173385#72) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 72 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 72).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 72 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 2763259016262009542185545 = (2763259016262009542185545#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 2762584392478742450012160) (d := 674623783267092173385)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_72_add {bv1: BitVec 18} {bv2: BitVec 72} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 72 +
    Normalize.normalize_unpacked bv2.toNat 24 =
    Normalize.normalize_unpacked (bv1.toNat <<< 72 + bv2.toNat) 30
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 72 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 176847902416985343607701504 = (176847902416985343607701504#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 674623783267092173385 = (674623783267092173385#72).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 72 &&& 176847902416985343607701504#192)
      (BitVec.setWidth 192 (bv2 &&& 674623783267092173385#72))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 674623783267092173385#72) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 72 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 72).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 72 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 176848577040768610699874889 = (176848577040768610699874889#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 176847902416985343607701504) (d := 674623783267092173385)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_75_add {bv1: BitVec 9} {bv2: BitVec 75} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 75 +
    Normalize.normalize_unpacked bv2.toNat 25 =
    Normalize.normalize_unpacked (bv1.toNat <<< 75 + bv2.toNat) 28
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 75 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 2757862025995872804798464 = (2757862025995872804798464#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 5396990266136737387081 = (5396990266136737387081#75).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 75 &&& 2757862025995872804798464#192)
      (BitVec.setWidth 192 (bv2 &&& 5396990266136737387081#75))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 5396990266136737387081#75) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 75 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 75).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 75 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 2763259016262009542185545 = (2763259016262009542185545#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_81_add {bv1: BitVec 9} {bv2: BitVec 81} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 81 +
    Normalize.normalize_unpacked bv2.toNat 27 =
    Normalize.normalize_unpacked (bv1.toNat <<< 81 + bv2.toNat) 30
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 81 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 176503169663735859507101696 = (176503169663735859507101696#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 345407377032751192773193 = (345407377032751192773193#81).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 81 &&& 176503169663735859507101696#192)
      (BitVec.setWidth 192 (bv2 &&& 345407377032751192773193#81))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 345407377032751192773193#81) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 81 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 81).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 81 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 176848577040768610699874889 = (176848577040768610699874889#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_84_add {bv1: BitVec 9} {bv2: BitVec 84} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 84 +
    Normalize.normalize_unpacked bv2.toNat 28 =
    Normalize.normalize_unpacked (bv1.toNat <<< 84 + bv2.toNat) 31
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 84 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 1412025357309886876056813568 = (1412025357309886876056813568#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 2763259016262009542185545 = (2763259016262009542185545#84).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 84 &&& 1412025357309886876056813568#192)
      (BitVec.setWidth 192 (bv2 &&& 2763259016262009542185545#84))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 2763259016262009542185545#84) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 84 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 84).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 84 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 1414788616326148885598999113 = (1414788616326148885598999113#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_84_add {bv1: BitVec 12} {bv2: BitVec 84} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 84 +
    Normalize.normalize_unpacked bv2.toNat 28 =
    Normalize.normalize_unpacked (bv1.toNat <<< 84 + bv2.toNat) 32
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 84 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 11315545671592929075249807360 = (11315545671592929075249807360#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 2763259016262009542185545 = (2763259016262009542185545#84).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 84 &&& 11315545671592929075249807360#192)
      (BitVec.setWidth 192 (bv2 &&& 2763259016262009542185545#84))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 2763259016262009542185545#84) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 84 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 84).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 84 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 11318308930609191084791992905 = (11318308930609191084791992905#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 11315545671592929075249807360) (d := 2763259016262009542185545)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_90_add {bv1: BitVec 9} {bv2: BitVec 90} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 90 +
    Normalize.normalize_unpacked bv2.toNat 30 =
    Normalize.normalize_unpacked (bv1.toNat <<< 90 + bv2.toNat) 33
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 90 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 90369622867832760067636068352 = (90369622867832760067636068352#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 176848577040768610699874889 = (176848577040768610699874889#90).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 90 &&& 90369622867832760067636068352#192)
      (BitVec.setWidth 192 (bv2 &&& 176848577040768610699874889#90))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 176848577040768610699874889#90) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 90 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 90).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 90 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 90546471444873528678335943241 = (90546471444873528678335943241#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_6_shift_90_add {bv1: BitVec 18} {bv2: BitVec 90} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 90 +
    Normalize.normalize_unpacked bv2.toNat 30 =
    Normalize.normalize_unpacked (bv1.toNat <<< 90 + bv2.toNat) 36
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 90 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 46359616531198205914697303064576 = (46359616531198205914697303064576#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 176848577040768610699874889 = (176848577040768610699874889#90).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 90 &&& 46359616531198205914697303064576#192)
      (BitVec.setWidth 192 (bv2 &&& 176848577040768610699874889#90))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 176848577040768610699874889#90) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 90 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 90).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 90 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 46359793379775246683308002939465 = (46359793379775246683308002939465#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 46359616531198205914697303064576) (d := 176848577040768610699874889)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_93_add {bv1: BitVec 9} {bv2: BitVec 93} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 93 +
    Normalize.normalize_unpacked bv2.toNat 31 =
    Normalize.normalize_unpacked (bv1.toNat <<< 93 + bv2.toNat) 34
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 93 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 722956982942662080541088546816 = (722956982942662080541088546816#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 1414788616326148885598999113 = (1414788616326148885598999113#93).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 93 &&& 722956982942662080541088546816#192)
      (BitVec.setWidth 192 (bv2 &&& 1414788616326148885598999113#93))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 1414788616326148885598999113#93) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 93 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 93).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 93 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 724371771558988229426687545929 = (724371771558988229426687545929#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_96_add {bv1: BitVec 12} {bv2: BitVec 96} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 96 +
    Normalize.normalize_unpacked bv2.toNat 32 =
    Normalize.normalize_unpacked (bv1.toNat <<< 96 + bv2.toNat) 36
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 96 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 46348475070844637492223210946560 = (46348475070844637492223210946560#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 11318308930609191084791992905 = (11318308930609191084791992905#96).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 96 &&& 46348475070844637492223210946560#192)
      (BitVec.setWidth 192 (bv2 &&& 11318308930609191084791992905#96))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 11318308930609191084791992905#96) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 96 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 96).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 96 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 46359793379775246683308002939465 = (46359793379775246683308002939465#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 46348475070844637492223210946560) (d := 11318308930609191084791992905)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_99_add {bv1: BitVec 9} {bv2: BitVec 99} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 99 +
    Normalize.normalize_unpacked bv2.toNat 33 =
    Normalize.normalize_unpacked (bv1.toNat <<< 99 + bv2.toNat) 36
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 99 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 46269246908330373154629666996224 = (46269246908330373154629666996224#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 90546471444873528678335943241 = (90546471444873528678335943241#99).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 99 &&& 46269246908330373154629666996224#192)
      (BitVec.setWidth 192 (bv2 &&& 90546471444873528678335943241#99))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 90546471444873528678335943241#99) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 99 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 99).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 99 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 46359793379775246683308002939465 = (46359793379775246683308002939465#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_102_add {bv1: BitVec 9} {bv2: BitVec 102} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 102 +
    Normalize.normalize_unpacked bv2.toNat 34 =
    Normalize.normalize_unpacked (bv1.toNat <<< 102 + bv2.toNat) 37
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 102 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 370153975266642985237037335969792 = (370153975266642985237037335969792#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 724371771558988229426687545929 = (724371771558988229426687545929#102).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 102 &&& 370153975266642985237037335969792#192)
      (BitVec.setWidth 192 (bv2 &&& 724371771558988229426687545929#102))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 724371771558988229426687545929#102) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 102 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 102).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 102 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 370878347038201973466464023515721 = (370878347038201973466464023515721#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_108_add {bv1: BitVec 9} {bv2: BitVec 108} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 108 +
    Normalize.normalize_unpacked bv2.toNat 36 =
    Normalize.normalize_unpacked (bv1.toNat <<< 108 + bv2.toNat) 39
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 108 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 23689854417065151055170389502066688 = (23689854417065151055170389502066688#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 46359793379775246683308002939465 = (46359793379775246683308002939465#108).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 108 &&& 23689854417065151055170389502066688#192)
      (BitVec.setWidth 192 (bv2 &&& 46359793379775246683308002939465#108))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 46359793379775246683308002939465#108) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 108 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 108).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 108 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 23736214210444926301853697505006153 = (23736214210444926301853697505006153#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_108_add {bv1: BitVec 12} {bv2: BitVec 108} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 108 +
    Normalize.normalize_unpacked bv2.toNat 36 =
    Normalize.normalize_unpacked (bv1.toNat <<< 108 + bv2.toNat) 40
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 108 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 189843353890179635168146272037109760 = (189843353890179635168146272037109760#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 46359793379775246683308002939465 = (46359793379775246683308002939465#108).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 108 &&& 189843353890179635168146272037109760#192)
      (BitVec.setWidth 192 (bv2 &&& 46359793379775246683308002939465#108))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 46359793379775246683308002939465#108) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 108 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 108).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 108 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 189889713683559410414829580040049225 = (189889713683559410414829580040049225#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 189843353890179635168146272037109760) (d := 46359793379775246683308002939465)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_108_add {bv1: BitVec 18} {bv2: BitVec 108} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 108 +
    Normalize.normalize_unpacked bv2.toNat 36 =
    Normalize.normalize_unpacked (bv1.toNat <<< 108 + bv2.toNat) 42
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 108 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 12152895315954422491302409814560210944 = (12152895315954422491302409814560210944#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 46359793379775246683308002939465 = (46359793379775246683308002939465#108).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 108 &&& 12152895315954422491302409814560210944#192)
      (BitVec.setWidth 192 (bv2 &&& 46359793379775246683308002939465#108))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 46359793379775246683308002939465#108) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 108 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 108).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 108 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 12152941675747802266549093122563150409 = (12152941675747802266549093122563150409#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 12152895315954422491302409814560210944) (d := 46359793379775246683308002939465)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_111_add {bv1: BitVec 9} {bv2: BitVec 111} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 111 +
    Normalize.normalize_unpacked bv2.toNat 37 =
    Normalize.normalize_unpacked (bv1.toNat <<< 111 + bv2.toNat) 40
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 111 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 189518835336521208441363116016533504 = (189518835336521208441363116016533504#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 370878347038201973466464023515721 = (370878347038201973466464023515721#111).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 111 &&& 189518835336521208441363116016533504#192)
      (BitVec.setWidth 192 (bv2 &&& 370878347038201973466464023515721#111))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 370878347038201973466464023515721#111) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 111 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 111).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 111 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 189889713683559410414829580040049225 = (189889713683559410414829580040049225#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_117_add {bv1: BitVec 9} {bv2: BitVec 117} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 117 +
    Normalize.normalize_unpacked bv2.toNat 39 =
    Normalize.normalize_unpacked (bv1.toNat <<< 117 + bv2.toNat) 42
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 117 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 12129205461537357340247239425058144256 = (12129205461537357340247239425058144256#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 23736214210444926301853697505006153 = (23736214210444926301853697505006153#117).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 117 &&& 12129205461537357340247239425058144256#192)
      (BitVec.setWidth 192 (bv2 &&& 23736214210444926301853697505006153#117))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 23736214210444926301853697505006153#117) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 117 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 117).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 117 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 12152941675747802266549093122563150409 = (12152941675747802266549093122563150409#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_120_add {bv1: BitVec 9} {bv2: BitVec 120} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 120 +
    Normalize.normalize_unpacked bv2.toNat 40 =
    Normalize.normalize_unpacked (bv1.toNat <<< 120 + bv2.toNat) 43
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 120 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 97033643692298858721977915400465154048 = (97033643692298858721977915400465154048#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 189889713683559410414829580040049225 = (189889713683559410414829580040049225#120).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 120 &&& 97033643692298858721977915400465154048#192)
      (BitVec.setWidth 192 (bv2 &&& 189889713683559410414829580040049225#120))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 189889713683559410414829580040049225#120) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 120 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 120).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 120 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 97223533405982418132392744980505203273 = (97223533405982418132392744980505203273#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_120_add {bv1: BitVec 12} {bv2: BitVec 120} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 120 +
    Normalize.normalize_unpacked bv2.toNat 40 =
    Normalize.normalize_unpacked (bv1.toNat <<< 120 + bv2.toNat) 44
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 120 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 777598377534175785648727130264001576960 = (777598377534175785648727130264001576960#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 189889713683559410414829580040049225 = (189889713683559410414829580040049225#120).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 120 &&& 777598377534175785648727130264001576960#192)
      (BitVec.setWidth 192 (bv2 &&& 189889713683559410414829580040049225#120))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 189889713683559410414829580040049225#120) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 120 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 120).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 120 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 777788267247859345059141959844041626185 = (777788267247859345059141959844041626185#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 777598377534175785648727130264001576960) (d := 189889713683559410414829580040049225)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_126_add {bv1: BitVec 9} {bv2: BitVec 126} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 126 +
    Normalize.normalize_unpacked bv2.toNat 42 =
    Normalize.normalize_unpacked (bv1.toNat <<< 126 + bv2.toNat) 45
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 126 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 6210153196307126958206586585629769859072 = (6210153196307126958206586585629769859072#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 12152941675747802266549093122563150409 = (12152941675747802266549093122563150409#126).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 126 &&& 6210153196307126958206586585629769859072#192)
      (BitVec.setWidth 192 (bv2 &&& 12152941675747802266549093122563150409#126))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 12152941675747802266549093122563150409#126) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 126 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 126).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 126 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 6222306137982874760473135678752333009481 = (6222306137982874760473135678752333009481#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_6_shift_126_add {bv1: BitVec 18} {bv2: BitVec 126} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 126 +
    Normalize.normalize_unpacked bv2.toNat 42 =
    Normalize.normalize_unpacked (bv1.toNat <<< 126 + bv2.toNat) 48
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 126 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 3185808589705556129559978918428071937703936 = (3185808589705556129559978918428071937703936#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 12152941675747802266549093122563150409 = (12152941675747802266549093122563150409#126).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 126 &&& 3185808589705556129559978918428071937703936#192)
      (BitVec.setWidth 192 (bv2 &&& 12152941675747802266549093122563150409#126))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& _) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 126 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 126).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 126 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 3185820742647231877362245467521194500854345 = (3185820742647231877362245467521194500854345#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 3185808589705556129559978918428071937703936) (d := 12152941675747802266549093122563150409)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_129_add {bv1: BitVec 9} {bv2: BitVec 129} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 129 +
    Normalize.normalize_unpacked bv2.toNat 43 =
    Normalize.normalize_unpacked (bv1.toNat <<< 129 + bv2.toNat) 46
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 129 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 49681225570457015665652692685038158872576 = (49681225570457015665652692685038158872576#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 97223533405982418132392744980505203273 = (97223533405982418132392744980505203273#129).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 129 &&& 49681225570457015665652692685038158872576#192)
      (BitVec.setWidth 192 (bv2 &&& 97223533405982418132392744980505203273#129))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 97223533405982418132392744980505203273#129) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 129 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 129).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 129 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 49778449103862998083785085430018664075849 = (49778449103862998083785085430018664075849#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_132_add {bv1: BitVec 12} {bv2: BitVec 132} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 132 +
    Normalize.normalize_unpacked bv2.toNat 44 =
    Normalize.normalize_unpacked (bv1.toNat <<< 132 + bv2.toNat) 48
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 132 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 3185042954379984018017186325561350459228160 = (3185042954379984018017186325561350459228160#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 777788267247859345059141959844041626185 = (777788267247859345059141959844041626185#132).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 132 &&& 3185042954379984018017186325561350459228160#192)
      (BitVec.setWidth 192 (bv2 &&& 777788267247859345059141959844041626185#132))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 777788267247859345059141959844041626185#132) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 132 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 132).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 132 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 3185820742647231877362245467521194500854345 = (3185820742647231877362245467521194500854345#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 3185042954379984018017186325561350459228160) (d := 777788267247859345059141959844041626185)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_135_add {bv1: BitVec 9} {bv2: BitVec 135} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 135 +
    Normalize.normalize_unpacked bv2.toNat 45 =
    Normalize.normalize_unpacked (bv1.toNat <<< 135 + bv2.toNat) 48
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 135 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 3179598436509249002601772331842442167844864 = (3179598436509249002601772331842442167844864#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 6222306137982874760473135678752333009481 = (6222306137982874760473135678752333009481#135).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 135 &&& 3179598436509249002601772331842442167844864#192)
      (BitVec.setWidth 192 (bv2 &&& 6222306137982874760473135678752333009481#135))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 6222306137982874760473135678752333009481#135) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 135 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 135).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 135 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 3185820742647231877362245467521194500854345 = (3185820742647231877362245467521194500854345#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_138_add {bv1: BitVec 9} {bv2: BitVec 138} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 138 +
    Normalize.normalize_unpacked bv2.toNat 46 =
    Normalize.normalize_unpacked (bv1.toNat <<< 138 + bv2.toNat) 49
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 138 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 25436787492073992020814178654739537342758912 = (25436787492073992020814178654739537342758912#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 49778449103862998083785085430018664075849 = (49778449103862998083785085430018664075849#138).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 138 &&& 25436787492073992020814178654739537342758912#192)
      (BitVec.setWidth 192 (bv2 &&& 49778449103862998083785085430018664075849#138))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 49778449103862998083785085430018664075849#138) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 138 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 138).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 138 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 25486565941177855018897963740169556006834761 = (25486565941177855018897963740169556006834761#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_144_add {bv1: BitVec 9} {bv2: BitVec 144} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 144 +
    Normalize.normalize_unpacked bv2.toNat 48 =
    Normalize.normalize_unpacked (bv1.toNat <<< 144 + bv2.toNat) 51
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 144 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 1627954399492735489332107433903330389936570368 = (1627954399492735489332107433903330389936570368#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 3185820742647231877362245467521194500854345 = (3185820742647231877362245467521194500854345#144).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 144 &&& 1627954399492735489332107433903330389936570368#192)
      (BitVec.setWidth 192 (bv2 &&& 3185820742647231877362245467521194500854345#144))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 3185820742647231877362245467521194500854345#144) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 144 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 144).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 144 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 1631140220235382721209469679370851584437424713 = (1631140220235382721209469679370851584437424713#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_144_add {bv1: BitVec 12} {bv2: BitVec 144} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 144 +
    Normalize.normalize_unpacked bv2.toNat 48 =
    Normalize.normalize_unpacked (bv1.toNat <<< 144 + bv2.toNat) 52
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 144 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 13045935941140414537798395189499291480998543360 = (13045935941140414537798395189499291480998543360#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 3185820742647231877362245467521194500854345 = (3185820742647231877362245467521194500854345#144).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 144 &&& 13045935941140414537798395189499291480998543360#192)
      (BitVec.setWidth 192 (bv2 &&& 3185820742647231877362245467521194500854345#144))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 3185820742647231877362245467521194500854345#144) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 144 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 144).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 144 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 13049121761883061769675757434966812675499397705 = (13049121761883061769675757434966812675499397705#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 13045935941140414537798395189499291480998543360) (d := 3185820742647231877362245467521194500854345)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_144_add {bv1: BitVec 18} {bv2: BitVec 144} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 144 +
    Normalize.normalize_unpacked bv2.toNat 48 =
    Normalize.normalize_unpacked (bv1.toNat <<< 144 + bv2.toNat) 54
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 144 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 835140606939773306027371113592408490037460598784 = (835140606939773306027371113592408490037460598784#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 3185820742647231877362245467521194500854345 = (3185820742647231877362245467521194500854345#144).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 144 &&& 835140606939773306027371113592408490037460598784#192)
      (BitVec.setWidth 192 (bv2 &&& 3185820742647231877362245467521194500854345#144))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& _) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 144 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 144).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 144 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 835143792760515953259248475837876011231961453129 = (835143792760515953259248475837876011231961453129#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 835140606939773306027371113592408490037460598784) (d := 3185820742647231877362245467521194500854345)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_147_add {bv1: BitVec 9} {bv2: BitVec 147} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 147 +
    Normalize.normalize_unpacked bv2.toNat 49 =
    Normalize.normalize_unpacked (bv1.toNat <<< 147 + bv2.toNat) 52
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 147 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 13023635195941883914656859471226643119492562944 = (13023635195941883914656859471226643119492562944#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 25486565941177855018897963740169556006834761 = (25486565941177855018897963740169556006834761#147).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 147 &&& 13023635195941883914656859471226643119492562944#192)
      (BitVec.setWidth 192 (bv2 &&& 25486565941177855018897963740169556006834761#147))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 25486565941177855018897963740169556006834761#147) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 147 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 147).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 147 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 13049121761883061769675757434966812675499397705 = (13049121761883061769675757434966812675499397705#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_153_add {bv1: BitVec 9} {bv2: BitVec 153} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 153 +
    Normalize.normalize_unpacked bv2.toNat 51 =
    Normalize.normalize_unpacked (bv1.toNat <<< 153 + bv2.toNat) 54
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 153 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 833512652540280570538039006158505159647524028416 = (833512652540280570538039006158505159647524028416#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 1631140220235382721209469679370851584437424713 = (1631140220235382721209469679370851584437424713#153).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 153 &&& 833512652540280570538039006158505159647524028416#192)
      (BitVec.setWidth 192 (bv2 &&& 1631140220235382721209469679370851584437424713#153))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 1631140220235382721209469679370851584437424713#153) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 153 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 153).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 153 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 835143792760515953259248475837876011231961453129 = (835143792760515953259248475837876011231961453129#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_156_add {bv1: BitVec 9} {bv2: BitVec 156} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 156 +
    Normalize.normalize_unpacked bv2.toNat 52 =
    Normalize.normalize_unpacked (bv1.toNat <<< 156 + bv2.toNat) 55
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 156 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 6668101220322244564304312049268041277180192227328 = (6668101220322244564304312049268041277180192227328#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 13049121761883061769675757434966812675499397705 = (13049121761883061769675757434966812675499397705#156).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 156 &&& 6668101220322244564304312049268041277180192227328#192)
      (BitVec.setWidth 192 (bv2 &&& 13049121761883061769675757434966812675499397705#156))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 13049121761883061769675757434966812675499397705#156) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 156 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 156).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 156 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 6681150342084127626073987806703008089855691625033 = (6681150342084127626073987806703008089855691625033#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_156_add {bv1: BitVec 12} {bv2: BitVec 156} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 156 +
    Normalize.normalize_unpacked bv2.toNat 52 =
    Normalize.normalize_unpacked (bv1.toNat <<< 156 + bv2.toNat) 56
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 156 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 53436153614911137946822226696189097906170033602560 = (53436153614911137946822226696189097906170033602560#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 13049121761883061769675757434966812675499397705 = (13049121761883061769675757434966812675499397705#156).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 156 &&& 53436153614911137946822226696189097906170033602560#192)
      (BitVec.setWidth 192 (bv2 &&& 13049121761883061769675757434966812675499397705#156))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 13049121761883061769675757434966812675499397705#156) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 156 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 156).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 156 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 53449202736673021008591902453624064718845533000265 = (53449202736673021008591902453624064718845533000265#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 53436153614911137946822226696189097906170033602560) (d := 13049121761883061769675757434966812675499397705)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_162_add {bv1: BitVec 9} {bv2: BitVec 162} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 162 +
    Normalize.normalize_unpacked bv2.toNat 54 =
    Normalize.normalize_unpacked (bv1.toNat <<< 162 + bv2.toNat) 57
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 162 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 426758478100623652115475971153154641739532302548992 = (426758478100623652115475971153154641739532302548992#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 835143792760515953259248475837876011231961453129 = (835143792760515953259248475837876011231961453129#162).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 162 &&& 426758478100623652115475971153154641739532302548992#192)
      (BitVec.setWidth 192 (bv2 &&& 835143792760515953259248475837876011231961453129#162))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 835143792760515953259248475837876011231961453129#162) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 162 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 162).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 162 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 427593621893384168068735219628992517750764264002121 = (427593621893384168068735219628992517750764264002121#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_6_shift_162_add {bv1: BitVec 18} {bv2: BitVec 162} :
    Normalize.normalize_unpacked bv1.toNat 6 <<< 162 +
    Normalize.normalize_unpacked bv2.toNat 54 =
    Normalize.normalize_unpacked (bv1.toNat <<< 162 + bv2.toNat) 60
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 18 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 162 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 218927099265619933535239173201568331212380071207632896 = (218927099265619933535239173201568331212380071207632896#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 835143792760515953259248475837876011231961453129 = (835143792760515953259248475837876011231961453129#162).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 162 &&& 218927099265619933535239173201568331212380071207632896#192)
      (BitVec.setWidth 192 (bv2 &&& 835143792760515953259248475837876011231961453129#162))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& _) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 162 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 162).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 162 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 218927934409412694051192432450044169088391303169086025 = (218927934409412694051192432450044169088391303169086025#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 218927099265619933535239173201568331212380071207632896) (d := 835143792760515953259248475837876011231961453129)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_165_add {bv1: BitVec 9} {bv2: BitVec 165} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 165 +
    Normalize.normalize_unpacked bv2.toNat 55 =
    Normalize.normalize_unpacked (bv1.toNat <<< 165 + bv2.toNat) 58
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 165 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 3414067824804989216923807769225237133916258420391936 = (3414067824804989216923807769225237133916258420391936#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 6681150342084127626073987806703008089855691625033 = (6681150342084127626073987806703008089855691625033#165).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 165 &&& 3414067824804989216923807769225237133916258420391936#192)
      (BitVec.setWidth 192 (bv2 &&& 6681150342084127626073987806703008089855691625033#165))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 6681150342084127626073987806703008089855691625033#165) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 165 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 165).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 165 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 3420748975147073344549881757031940142006114112016969 = (3420748975147073344549881757031940142006114112016969#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_168_add {bv1: BitVec 12} {bv2: BitVec 168} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 168 +
    Normalize.normalize_unpacked bv2.toNat 56 =
    Normalize.normalize_unpacked (bv1.toNat <<< 168 + bv2.toNat) 60
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 168 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 218874485206676021030183840547590545023672457636085760 = (218874485206676021030183840547590545023672457636085760#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 53449202736673021008591902453624064718845533000265 = (53449202736673021008591902453624064718845533000265#168).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 168 &&& 218874485206676021030183840547590545023672457636085760#192)
      (BitVec.setWidth 192 (bv2 &&& 53449202736673021008591902453624064718845533000265#168))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 53449202736673021008591902453624064718845533000265#168) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 168 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 168).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 168 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 218927934409412694051192432450044169088391303169086025 = (218927934409412694051192432450044169088391303169086025#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 218874485206676021030183840547590545023672457636085760) (d := 53449202736673021008591902453624064718845533000265)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_171_add {bv1: BitVec 9} {bv2: BitVec 171} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 171 +
    Normalize.normalize_unpacked bv2.toNat 57 =
    Normalize.normalize_unpacked (bv1.toNat <<< 171 + bv2.toNat) 60
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 171 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 218500340787519309883123697230415176570640538905083904 = (218500340787519309883123697230415176570640538905083904#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 427593621893384168068735219628992517750764264002121 = (427593621893384168068735219628992517750764264002121#171).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 171 &&& 218500340787519309883123697230415176570640538905083904#192)
      (BitVec.setWidth 192 (bv2 &&& 427593621893384168068735219628992517750764264002121#171))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 427593621893384168068735219628992517750764264002121#171) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 171 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 171).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 171 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 218927934409412694051192432450044169088391303169086025 = (218927934409412694051192432450044169088391303169086025#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_174_add {bv1: BitVec 9} {bv2: BitVec 174} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 174 +
    Normalize.normalize_unpacked bv2.toNat 58 =
    Normalize.normalize_unpacked (bv1.toNat <<< 174 + bv2.toNat) 61
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 174 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 1748002726300154479064989577843321412565124311240671232 = (1748002726300154479064989577843321412565124311240671232#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 3420748975147073344549881757031940142006114112016969 = (3420748975147073344549881757031940142006114112016969#174).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 174 &&& 1748002726300154479064989577843321412565124311240671232#192)
      (BitVec.setWidth 192 (bv2 &&& 3420748975147073344549881757031940142006114112016969#174))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 3420748975147073344549881757031940142006114112016969#174) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 174 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 174).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 174 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 1751423475275301552409539459600353352707130425352688201 = (1751423475275301552409539459600353352707130425352688201#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_3_shift_180_add {bv1: BitVec 9} {bv2: BitVec 180} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 180 +
    Normalize.normalize_unpacked bv2.toNat 60 =
    Normalize.normalize_unpacked (bv1.toNat <<< 180 + bv2.toNat) 63
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 180 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 111872174483209886660159332981972570404167955919402958848 = (111872174483209886660159332981972570404167955919402958848#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 218927934409412694051192432450044169088391303169086025 = (218927934409412694051192432450044169088391303169086025#180).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 180 &&& 111872174483209886660159332981972570404167955919402958848#192)
      (BitVec.setWidth 192 (bv2 &&& 218927934409412694051192432450044169088391303169086025#180))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 218927934409412694051192432450044169088391303169086025#180) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 180 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 180).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 180 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 112091102417619299354210525414422614573256347222572044873 = (112091102417619299354210525414422614573256347222572044873#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_4_shift_180_add {bv1: BitVec 12} {bv2: BitVec 180} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 180 +
    Normalize.normalize_unpacked bv2.toNat 60 =
    Normalize.normalize_unpacked (bv1.toNat <<< 180 + bv2.toNat) 64
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 180 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 896509891406544982139633010882930872416962386477407272960 = (896509891406544982139633010882930872416962386477407272960#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 218927934409412694051192432450044169088391303169086025 = (218927934409412694051192432450044169088391303169086025#180).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 180 &&& 896509891406544982139633010882930872416962386477407272960#192)
      (BitVec.setWidth 192 (bv2 &&& 218927934409412694051192432450044169088391303169086025#180))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 218927934409412694051192432450044169088391303169086025#180) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 180 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 180).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 180 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 896728819340954394833684203315380916586050777780576358985 = (896728819340954394833684203315380916586050777780576358985#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 896509891406544982139633010882930872416962386477407272960) (d := 218927934409412694051192432450044169088391303169086025)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_6_shift_180_add {bv1: BitVec 12} {bv2: BitVec 180} :
    Normalize.normalize_unpacked bv1.toNat 4 <<< 180 +
    Normalize.normalize_unpacked bv2.toNat 60 =
    Normalize.normalize_unpacked (bv1.toNat <<< 180 + bv2.toNat) 64
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 12 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 180 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 896509891406544982139633010882930872416962386477407272960 = (896509891406544982139633010882930872416962386477407272960#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 218927934409412694051192432450044169088391303169086025 = (218927934409412694051192432450044169088391303169086025#180).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 180 &&& 896509891406544982139633010882930872416962386477407272960#192)
      (BitVec.setWidth 192 (bv2 &&& 218927934409412694051192432450044169088391303169086025#180))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& _) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 180 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 180).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 180 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 896728819340954394833684203315380916586050777780576358985 = (896728819340954394833684203315380916586050777780576358985#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (b := 896509891406544982139633010882930872416962386477407272960) (d := 218927934409412694051192432450044169088391303169086025)
          (Nat.and_le_right)
          (Nat.and_le_right)
        )
        (by trivial)

  lemma normalize_3_shift_183_add {bv1: BitVec 9} {bv2: BitVec 183} :
    Normalize.normalize_unpacked bv1.toNat 3 <<< 183 +
    Normalize.normalize_unpacked bv2.toNat 61 =
    Normalize.normalize_unpacked (bv1.toNat <<< 183 + bv2.toNat) 64
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 9 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 183 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 894977395865679093281274663855780563233343647355223670784 = (894977395865679093281274663855780563233343647355223670784#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 1751423475275301552409539459600353352707130425352688201 = (1751423475275301552409539459600353352707130425352688201#183).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 183 &&& 894977395865679093281274663855780563233343647355223670784#192)
      (BitVec.setWidth 192 (bv2 &&& 1751423475275301552409539459600353352707130425352688201#183))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 1751423475275301552409539459600353352707130425352688201#183) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 183 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 183).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 183 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 896728819340954394833684203315380916586050777780576358985 = (896728819340954394833684203315380916586050777780576358985#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_1_shift_189_add {bv1: BitVec 3} {bv2: BitVec 189} :
    Normalize.normalize_unpacked bv1.toNat 1 <<< 189 +
    Normalize.normalize_unpacked bv2.toNat 63 =
    Normalize.normalize_unpacked (bv1.toNat <<< 189 + bv2.toNat) 64
  := by
    rewrite [
      ←bitvec_setWidth_toNat bv1 (show 3 ≤ 192 by trivial),
      ←bitvec_setWidth_toNat bv2 (show 189 ≤ 192 by trivial)
    ]
    simp only [Normalize.normalize_unpacked_toNat, keccak_constants]
    simp [Normalize.normalize_unpacked_to_bitvec, Normalize.mask.eq_def, keccak_constants]
    rewrite [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp [Nat.and_assoc, Nat.shiftLeft_and_distrib, Normalize.mask_bitvec.eq_def, -Nat.and_one_is_mod]
    rewrite [←bitvec_setWidth_shift_toNat (width2 := 192) (by trivial)]
    rewrite [show 784637716923335095479473677900958302012794430558004314112 = (784637716923335095479473677900958302012794430558004314112#192).toNat by decide, ←BitVec.toNat_and]
    rewrite [show 112091102417619299354210525414422614573256347222572044873 = (112091102417619299354210525414422614573256347222572044873#189).toNat by decide, ←BitVec.toNat_and]
    have := BitVec.toNat_add
      (BitVec.setWidth 192 bv1 <<< 189 &&& 784637716923335095479473677900958302012794430558004314112#192)
      (BitVec.setWidth 192 (bv2 &&& 112091102417619299354210525414422614573256347222572044873#189))
    rewrite [Nat.mod_eq_of_lt, bitvec_setWidth_toNat (bv2 &&& 112091102417619299354210525414422614573256347222572044873#189) (by trivial)] at this
    . rewrite [←this]; clear this
      rewrite [←bitvec_setWidth_toNat bv2 (show 189 ≤ 192 by trivial)]
      have :
        (BitVec.setWidth 192 bv1 <<< 189).toNat + (BitVec.setWidth 192 bv2).toNat =
        (BitVec.setWidth 192 bv1 <<< 189 + BitVec.setWidth 192 bv2).toNat
      := by
        simp; rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rewrite [Nat.mod_eq_of_lt (by omega)]
        omega
      rewrite [this]
      rewrite [show 896728819340954394833684203315380916586050777780576358985 = (896728819340954394833684203315380916586050777780576358985#192).toNat by decide, ←BitVec.toNat_and, ←BitVec.toNat_eq]
      bv_decide
    . simp
      rewrite [
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)
      ]
      exact lt_of_le_of_lt
        (Nat.add_le_add (Nat.and_le_right) (Nat.and_le_right))
        (by trivial)

  lemma normalize_unpacked_and:
    normalize_unpacked (x &&& y) k =
    (normalize_unpacked x k) &&& (normalize_unpacked y k)
  := by
    simp [
      normalize_unpacked.eq_def,
    ]
    rewrite [
      Nat.and_assoc
    ]
    have (a b: ℕ): a &&& b &&& b = a &&& b := by rw [Nat.and_assoc, Nat.and_self]
    rewrite [
      ←this,
      Nat.and_assoc x,
      Nat.and_comm y
    ]
    simp [←Nat.and_assoc]

  lemma normalize_unpacked_xor:
    normalize_unpacked (x ^^^ y) k =
    (normalize_unpacked x k) ^^^ (normalize_unpacked y k)
  := by
    simp [normalize_unpacked.eq_def, Nat.and_xor_distrib_right]

  lemma normalize_unpacked_585_4:
    normalize_unpacked 585 4 = 585
  := by decide

  lemma normalize_unpacked_4095_4:
    normalize_unpacked 4095 4 = 585
  := by decide

  lemma and_normalize:
    x &&& normalize_unpacked y k =
    normalize_unpacked x k &&& normalize_unpacked y k
  := by
    rewrite [←normalize_unpacked_and]
    simp [normalize_unpacked.eq_def]
    rw [←Nat.and_assoc, ←Nat.and_assoc]

  -- lemma normalize_decode_step (P_Prime: Nat.Prime P) (x y : ZMod P) (h_x: x.val < 2^m) (h_y: y.val < 2^n) (h_P: 2^(BIT_COUNT*(n+m)) ≤ P):
  --   2^(BIT_COUNT*n) * ((normalize_unpacked x.val m): ZMod P) + ((normalize_unpacked y.val n): ZMod P) =
  --   normalize_unpacked (2^(BIT_COUNT*n)*x + y).val (n+m)
  -- := by
  --   simp [keccak_constants]
  --   have ne_zero: NeZero P := by
  --     constructor; simp_all [Nat.Prime.ne_zero]
  --   have one_lt_p: Fact (1 < P) := by
  --     constructor; simp_all [Nat.Prime.one_lt]
  --   rewrite [ZMod.val_add, ZMod.val_mul, ZMod.val_pow]
  --   symm
  --   rewrite [ZMod.natCast_eq_iff]
  --   use 0
  --   simp
  --   set x' := x.val
  --   set y' := y.val
  --   rewrite [ZMod.val_add, ZMod.val_mul, ZMod.val_pow, ZMod.val_two_eq_two_mod]
  --   have : ((normalize_unpacked x' m): ZMod P).val = (normalize_unpacked x' m) % P := by simp
  --   rewrite [this]; clear this
  --   have : ((normalize_unpacked y' n): ZMod P).val = (normalize_unpacked y' n) % P := by simp
  --   rewrite [this]; clear this
  --   clear_value x' y'
  --   rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
  --   rewrite [normalize_unpacked_to_bitvec, normalize_unpacked_to_bitvec, normalize_unpacked_to_bitvec]
  --   all_goals sorry
  --   -- have := BitVec.toNat_mul
  --   -- rewrite [mask_bitvec_ofNat]
  --   -- simp only [keccak_constants, BitVec.toNat_add]

  lemma normalize_unpacked_UInt64 :normalize_unpacked (UInt64_to_unpacked_Nat x) 64 = UInt64_to_unpacked_Nat x := by
    simp [UInt64_to_unpacked_Nat.eq_def, list_ops]
    rewrite [normalize_unpacked_toNat, ←BitVec.toNat_eq, BitVec.and_assoc]
    rewrite [List.foldr_filter]
    simp only [
      if_true_mask_else_self,
      keccak_constants,
      Nat.reduceMul,
      BitVec.setWidth_eq,
      BitVec.and_allOnes
    ]
    rewrite [list_foldr_or_and]; swap; decide
    rewrite [List.foldr]; symm; rewrite [List.foldr]; symm
    rewrite [bitvec_and_or_distrib_right]
    rewrite [bitvec_if_and]
    simp only [mask_bitvec.eq_def]
    congr 1
    repeat (
      rewrite [List.foldr]; symm; rewrite [List.foldr]; symm
      rewrite [BitVec.and_assoc, BitVec.and_self]
      rewrite [bitvec_and_or_distrib_right, bitvec_if_and]
      congr 1
    )

  -- lemma add_eq_xor (x y: Nat):
  --   normalize_unpacked (normalize_unpacked x + normalize_unpacked y) = normalize_unpacked (x ^^^ y)
  -- := by
  --   simp only [
  --     normalize_unpacked_to_bitvec,
  --     BitVec.toNat_and,
  --     BitVec.toNat_ofNat,
  --     ←Nat.and_pow_two_sub_one_eq_mod,
  --     mask_and_2_pow_192_sub_one,
  --     mask_and_2_pow_192_sub_one',
  --     Nat.and_assoc
  --   ]
  --   rewrite [Nat.and_xor_distrib_right]
  --   have := normalize_unpacked_to_bitvec
  --   unfold normalize_unpacked at this
  --   rewrite [this, this, this]
  --   rewrite [mask_bitvec_ofNat]
  --   generalize BitVec.ofNat 192 x = bv_x
  --   generalize BitVec.ofNat 192 y = bv_y
  --   rewrite [
  --     ←BitVec.toNat_xor,
  --     ←BitVec.toNat_eq,
  --     ←BitVec.toNat_add_of_lt,
  --     BitVec.ofNat_toNat, BitVec.setWidth_eq
  --   ]
  --   . unfold mask_bitvec
  --     bv_decide
  --   . rewrite [BitVec.toNat_and, BitVec.toNat_and, mask_bitvec_toNat]
  --     have h_x := Nat.and_le_right (m := mask) (n := bv_x.toNat)
  --     have h_y := Nat.and_le_right (m := mask) (n := bv_y.toNat)
  --     unfold mask at h_x h_y ⊢
  --     simp
  --     omega

end Keccak.Soundness.Normalize

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

  lemma normalize_unpacked_4_le : normalize_unpacked x 4 ≤ 585 := by
    simp [
      normalize_unpacked.eq_def,
      keccak_constants,
      Nat.and_assoc,
      mask.eq_def,
      Nat.and_le_right
    ]

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

  -- lemma normalize_unpacked_UInt64 :normalize_unpacked (UInt64_to_unpacked_Nat x) = UInt64_to_unpacked_Nat x := by
  --   simp [UInt64_to_unpacked_Nat.eq_def, list_ops]
  --   rewrite [normalize_unpacked_toNat, ←BitVec.toNat_eq]
  --   rewrite [List.foldr_filter]
  --   simp only [if_true_mask_else_self]
  --   rewrite [list_foldr_or_and]; swap; decide
  --   rewrite [List.foldr]; symm; rewrite [List.foldr]; symm
  --   rewrite [bitvec_and_or_distrib_right]
  --   rewrite [bitvec_if_and]
  --   simp only [mask_bitvec.eq_def]
  --   congr 1
  --   repeat (
  --     rewrite [List.foldr]; symm; rewrite [List.foldr]; symm
  --     rewrite [BitVec.and_assoc, BitVec.and_self]
  --     rewrite [bitvec_and_or_distrib_right, bitvec_if_and]
  --     congr 1
  --   )

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

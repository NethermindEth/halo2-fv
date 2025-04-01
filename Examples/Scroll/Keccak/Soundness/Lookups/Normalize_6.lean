import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness.Lookups.Normalize_6

    lemma input_lt_P (h_a: a < 6) (h_b: b < 6) (h_c: c < 6) (h_P: P > 365): a + b * 8 + c * 64 < P := by omega
    lemma output_lt_P (h_a: a < 2) (h_b: b < 2) (h_c: c < 2) (h_P: P > 73): a + b * 8 + c * 64 < P := by omega

    lemma exists_3bit_of_lt_6 (h: x < 6): ∃ bv: BitVec 3, x = bv.toNat := by
      use BitVec.ofNat 3 x
      simp
      omega

    lemma bitvec_3_mod_2 {bv: BitVec 3}: bv.toNat % 2 = (bv &&& 1#3).toNat := by simp

    lemma pow_2_to_bitvec : 2 ^ k = (1#(k+1) <<< k).toNat := by
      simp [Nat.one_shiftLeft]
      rw [Nat.mod_eq_of_lt]
      exact Nat.pow_lt_pow_right (by trivial) (by omega)

    lemma bitvec_toNat_lt (bv: BitVec n): bv.toNat < 2^n := by bv_omega

    lemma bitvec_toNat_mul_2_pow {bv: BitVec n}: bv.toNat * 2^k = (BitVec.setWidth (n+k) bv <<< k).toNat := by
      rewrite [pow_2_to_bitvec]
      have : bv.toNat * (1#(k+1) <<< k).toNat = bv.toNat * (1#(k+1) <<< k).toNat % 2^(n+k) := by
        simp [Nat.shiftLeft_eq]
        rewrite [Nat.mod_eq_of_lt]
        . rw [Nat.mod_eq_of_lt]
          simp [pow_add, bitvec_toNat_lt]
        . exact Nat.pow_lt_pow_right (by trivial) (by omega)
      rewrite [this]
      simp
      rewrite [
        Nat.mod_eq_of_lt (a := 1 <<< k),
        Nat.mod_eq_of_lt,
        Nat.mod_eq_of_lt,
        Nat.mod_eq_of_lt
      ]
      . simp [Nat.shiftLeft_eq]
      . apply lt_of_lt_of_le (bitvec_toNat_lt bv) (Nat.pow_le_pow_right (by trivial) (by omega))
      . rewrite [Nat.mod_eq_of_lt]
        . rewrite [Nat.shiftLeft_eq, pow_add]
          exact (Nat.mul_lt_mul_right (a := 2^k) (b := bv.toNat) (c := 2^n) (by simp)).mpr (bitvec_toNat_lt bv)
        . apply lt_of_lt_of_le (bitvec_toNat_lt bv) (Nat.pow_le_pow_right (by trivial) (by omega))
      . simp [Nat.shiftLeft_eq]
        rewrite [pow_add]
        exact (Nat.mul_lt_mul_right (a := 2^k) (b := bv.toNat) (c := 2^n) (by simp)).mpr (bitvec_toNat_lt bv)
      . simp [Nat.shiftLeft_eq, Nat.pow_lt_pow_right]

    lemma bitvec_toNat_add (bv1: BitVec n) (bv2: BitVec m):
      bv1.toNat + bv2.toNat = (BitVec.setWidth (1 + max n m) bv1 + BitVec.setWidth (1 + max n m) bv2).toNat
    := by
      rewrite [BitVec.toNat_add]
      simp
      rw [Nat.mod_eq_of_lt]
      simp [Nat.pow_add]
      have := bitvec_toNat_lt bv1
      have := bitvec_toNat_lt bv2
      apply lt_of_lt_of_le (b := 2^n + 2^m)
      omega
      rewrite [two_mul]
      apply add_le_add <;> simp [Nat.pow_le_pow_right]

    lemma bitvec_toNat_eq (bv1: BitVec n) (bv2: BitVec m) (h: BitVec.setWidth (max n m) bv1 = BitVec.setWidth (max n m) bv2):
      bv1.toNat = bv2.toNat
    := by
      unfold BitVec.setWidth at h
      rewrite [dite_cond_eq_true, dite_cond_eq_true] at h
      apply BitVec.toNat_eq.mp at h
      simp [BitVec.toNat_setWidth] at h
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h
      . exact h
      . have := bitvec_toNat_lt bv2
        apply lt_of_lt_of_le this
        apply Nat.pow_le_pow_right <;> simp
      . have := bitvec_toNat_lt bv1
        apply lt_of_lt_of_le this
        apply Nat.pow_le_pow_right <;> simp
      all_goals simp

    lemma normalize_aux (h_a: a < 6) (h_b: b < 6) (h_c: c < 6) (h_P: P ≥ 366):
      (a % 2 + b % 2 * 8 + c % 2 * 64) % P = Normalize.normalize_unpacked ((a + b*8 + c*64) % P) 3
    := by
      rewrite [Nat.mod_eq_of_lt (b := P), Nat.mod_eq_of_lt (b := P)]
      . obtain ⟨bv_a, h_bv_a⟩ := exists_3bit_of_lt_6 h_a
        obtain ⟨bv_b, h_bv_b⟩ := exists_3bit_of_lt_6 h_b
        obtain ⟨bv_c, h_bv_c⟩ := exists_3bit_of_lt_6 h_c
        subst h_bv_a h_bv_b h_bv_c
        rewrite [bitvec_3_mod_2, bitvec_3_mod_2, bitvec_3_mod_2]
        have : (bv_b &&& 1#3).toNat * 8 = (BitVec.setWidth 6 (bv_b &&& 1#3) <<< 3).toNat := by
          convert bitvec_toNat_mul_2_pow <;> trivial
        rewrite [this]; clear this
        have : bv_b.toNat * 8 = (BitVec.setWidth 6 bv_b <<< 3).toNat := by
          convert bitvec_toNat_mul_2_pow <;> trivial
        rewrite [this]; clear this
        have : (bv_c &&& 1#3).toNat * 64 = (BitVec.setWidth 9 (bv_c &&& 1#3) <<< 6).toNat := by
          convert bitvec_toNat_mul_2_pow <;> trivial
        rewrite [this]; clear this
        have : bv_c.toNat * 64 = (BitVec.setWidth 9 bv_c <<< 6).toNat := by
          convert bitvec_toNat_mul_2_pow <;> trivial
        rewrite [this]; clear this
        simp only [bitvec_toNat_add]
        rewrite [Normalize.normalize_unpacked_toNat_small]
        apply bitvec_toNat_eq _ _
        . rewrite [Nat.max_eq_right (by simp), Nat.max_eq_right (by simp), Nat.max_eq_right (by simp)]
          simp [keccak_constants, Normalize.mask_bitvec.eq_def]
          bv_decide
        . simp
      . apply input_lt_P h_a h_b h_c h_P
      . exact output_lt_P (Nat.mod_lt a (by trivial)) (Nat.mod_lt b (by trivial)) (Nat.mod_lt c (by trivial)) (by omega)

    lemma output_eq_normalized_input [NeZero P] (h_row: row < 216) (h_P: P ≥ 366):
      (Lookups.Normalize_6.output_by_row P row).val = Normalize.normalize_unpacked (Lookups.Normalize_6.input_by_row P row |>.val) 3
    := by
      unfold Lookups.Normalize_6.input_by_row Lookups.Normalize_6.output_by_row Lookups.Normalize_6.input Lookups.Normalize_6.output
      simp [keccak_constants, ZMod.val_add, ZMod.val_mul]
      simp [OfNat.ofNat, Nat.mod_eq_of_lt (a := 8) (b := P) (by omega), Nat.mod_eq_of_lt (a := 64) (b := P) (by omega)]
      set a := row / 36
      have h_a : a < 6 := by omega
      set b := row / 6 % 6
      have h_b : row / 6 % 2 = b % 2 := by omega
      rewrite [h_b]
      have h_b' : b < 6 := by omega
      set c := row % 6
      have h_c : row % 2 = c % 2 := by omega
      have h_c' : c < 6 := by omega
      rewrite [h_c]
      rewrite [Nat.mod_eq_of_lt]
      . rewrite [Nat.mod_eq_of_lt (b := P)]
        . set bv_a := BitVec.ofNat 3 a
          set bv_b := BitVec.ofNat 3 b
          set bv_c := BitVec.ofNat 3 c
          have : a = bv_a.toNat := by unfold bv_a; simp; rw [Nat.mod_eq_of_lt]; omega
          have : b = bv_b.toNat := by unfold bv_b; simp; rw [Nat.mod_eq_of_lt]; omega
          have : c = bv_c.toNat := by unfold bv_c; simp; rw [Nat.mod_eq_of_lt]; omega
          simp_all [←Nat.and_one_is_mod]
          have {bv: BitVec 3}: bv.toNat &&& 1 = (bv &&& 1#3).toNat := by simp
          rewrite [this, this, this]
          have {bv: BitVec 3}: bv.toNat * 8 = (BitVec.setWidth 9 bv <<< 3).toNat := by
            simp
            rewrite [BitVec.toNat_mod_cancel_of_lt (x := bv) (m := 9) (by trivial)]
            rewrite [Nat.mod_eq_of_lt (a := bv.toNat <<< 3)]
            all_goals simp [Nat.shiftLeft_eq]
            rewrite [←BitVec.toNat_mod_cancel_of_lt (x := bv) (m := 4) (by trivial)]
            simp
            omega
          rewrite [this, BitVec.setWidth_and]
          have : (bv_a &&& 1#3).toNat = (BitVec.setWidth 9 bv_a &&& 1#9).toNat := by simp
          rewrite [this]
          have :
            (BitVec.setWidth 9 bv_a &&& 1#9).toNat + ((BitVec.setWidth 9 bv_b &&& BitVec.setWidth 9 1#3) <<< 3).toNat < 2^4
          := by
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^9) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 64 = (BitVec.setWidth 9 (bv &&& 1#3) <<< 6).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 512) (by omega)]
          rewrite [this]
          have :
            ((BitVec.setWidth 9 bv_a &&& 1#9) +
            (BitVec.setWidth 9 bv_b &&& BitVec.setWidth 9 1#3) <<< 3).toNat +
            (BitVec.setWidth 9 (bv_c &&& 1#3) <<< 6).toNat < 2^7
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 512) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 512) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^9) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have : bv_a.toNat = (BitVec.setWidth 9 bv_a).toNat := by simp; rw [Nat.mod_eq_of_lt (by omega)]
          rewrite [this]
          have : bv_b.toNat * 8 = (BitVec.setWidth 9 bv_b <<< 3).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_c.toNat * 64 = (BitVec.setWidth 9 bv_c <<< 6).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : (BitVec.setWidth 9 bv_a).toNat + (BitVec.setWidth 9 bv_b <<< 3).toNat < 2^6 := by omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^9) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have : (BitVec.setWidth 9 bv_a + BitVec.setWidth 9 bv_b <<< 3).toNat + (BitVec.setWidth 9 bv_c <<< 6).toNat < 2^9 := by
            simp
            rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
            . omega
            . omega
            . omega
            . omega
            . rewrite [Nat.mod_eq_of_lt, Nat.shiftLeft_eq]
              simp
              rewrite [←BitVec.toNat_mod_cancel]; omega
              rewrite [←BitVec.toNat_mod_cancel]; omega
          rewrite [←Nat.mod_eq_of_lt this, ←BitVec.toNat_add]
          have :
            (BitVec.setWidth 9 bv_a + BitVec.setWidth 9 bv_b <<< 3 + BitVec.setWidth 9 bv_c <<< 6).toNat =
            (BitVec.setWidth 192 (BitVec.setWidth 9 bv_a + BitVec.setWidth 9 bv_b <<< 3 + BitVec.setWidth 9 bv_c <<< 6)).toNat
          := by
            simp
            symm
            apply Nat.mod_eq_of_lt
            omega
          rewrite [this, Normalize.normalize_unpacked_toNat]
          have :
            ((BitVec.setWidth 9 bv_a &&& 1#9) + (BitVec.setWidth 9 bv_b &&& BitVec.setWidth 9 1#3) <<< 3 + BitVec.setWidth 9 (bv_c &&& 1#3) <<< 6).toNat =
            (BitVec.setWidth 192 ((BitVec.setWidth 9 bv_a &&& 1#9) + (BitVec.setWidth 9 bv_b &&& BitVec.setWidth 9 1#3) <<< 3 + BitVec.setWidth 9 (bv_c &&& 1#3) <<< 6)).toNat
          := by
            simp
            symm
            apply Nat.mod_eq_of_lt
            omega
          rewrite [this, ←BitVec.toNat_eq, Normalize.mask_bitvec.eq_def]
          simp [keccak_constants]
          bv_decide
        . apply input_lt_P <;> omega
      . apply output_lt_P
        . exact Nat.mod_lt _ (by trivial)
        . exact Nat.mod_lt _ (by trivial)
        . exact Nat.mod_lt _ (by trivial)
        . omega

end Keccak.Soundness.Lookups.Normalize_6

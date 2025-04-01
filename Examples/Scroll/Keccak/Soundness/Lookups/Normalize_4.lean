import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness.Lookups.Normalize_4
    lemma input_unrolled_lt_P (h_a: a < 4) (h_b: b < 4) (h_c: c < 4) (h_d: d < 4) (h_P: P > 1755): a + b * 8 + c * 64 + d*512 < P := by omega
    lemma input_range [NeZero P] (h_P: 8 < P) (h_row: row < 256): (Lookups.Normalize_4.input_by_row P row).val ≤ 1755 := by -- 3*(4 masked unpacked bits)
      unfold Lookups.Normalize_4.input_by_row
      simp [Lookups.Normalize_4.input_eval, keccak_constants, ZMod.val_add, ZMod.val_mul]
      apply le_trans (Nat.mod_le _ P)
      have : (8: ZMod P).val = 8 := by convert ZMod.val_cast_of_lt h_P
      have : Fact (1 < P) := by constructor; omega

      apply add_le_add (d := 1536)
      . apply add_le_add (d := 192)
        . apply add_le_add (d := 24)
          . omega
          . simp_all; omega
        . apply Nat.mul_le_mul (n₂ := 3) (m₂ := 64)
          . omega
          . convert ZMod.val_pow_le <;> simp_all
      . apply Nat.mul_le_mul (n₂ := 3) (m₂ := 512)
        . omega
        . convert ZMod.val_pow_le <;> simp_all
    lemma output_lt_P (h_a: a < 2) (h_b: b < 2) (h_c: c < 2) (h_d: d < 2) (h_P: P > 585): a + b * 8 + c * 64 + d*512 < P := by omega

    lemma output_eq_normalized_input [NeZero P] (h_row: row < 256) (h_P: P ≥ 1756):
      (Lookups.Normalize_4.output_by_row P row).val = Normalize.normalize_unpacked (Lookups.Normalize_4.input_by_row P row |>.val) 4
    := by
      unfold Lookups.Normalize_4.input_by_row Lookups.Normalize_4.output_by_row Lookups.Normalize_4.input Lookups.Normalize_4.output
      simp [keccak_constants, ZMod.val_add, ZMod.val_mul]
      simp [
        OfNat.ofNat,
        Nat.mod_eq_of_lt (a := 8) (b := P) (by omega),
        Nat.mod_eq_of_lt (a := 64) (b := P) (by omega),
        Nat.mod_eq_of_lt (a := 512) (b := P) (by omega),
      ]
      set a := row / 64
      have h_a: a < 4 := by omega
      set b := row / 16 % 4
      have h_b : row / 16 % 2 = b % 2 := by omega
      have h_b': b < 4 := by omega
      rewrite [h_b]
      set c := row / 4 % 4
      have h_c : row / 4 % 2 = c % 2 := by omega
      have h_c': c < 4 := by omega
      rewrite [h_c]
      set d := row % 4
      have h_d : row % 2 = d % 2 := by omega
      have h_d': d < 4 := by omega
      rewrite [h_d]
      rewrite [Nat.mod_eq_of_lt]
      . rewrite [Nat.mod_eq_of_lt (b := P)]
        . set bv_a := BitVec.ofNat 3 a
          set bv_b := BitVec.ofNat 3 b
          set bv_c := BitVec.ofNat 3 c
          set bv_d := BitVec.ofNat 3 d
          have : a = bv_a.toNat := by unfold bv_a; simp; rw [Nat.mod_eq_of_lt]; omega
          have : b = bv_b.toNat := by unfold bv_b; simp; rw [Nat.mod_eq_of_lt]; omega
          have : c = bv_c.toNat := by unfold bv_c; simp; rw [Nat.mod_eq_of_lt]; omega
          have : d = bv_d.toNat := by unfold bv_d; simp; rw [Nat.mod_eq_of_lt]; omega
          simp_all [←Nat.and_one_is_mod]
          have {bv: BitVec 3}: bv.toNat &&& 1 = (bv &&& 1#3).toNat := by simp
          rewrite [this, this, this, this]
          have {bv: BitVec 3}: bv.toNat * 8 = (BitVec.setWidth 12 bv <<< 3).toNat := by
            simp
            rewrite [BitVec.toNat_mod_cancel_of_lt (x := bv) (m := 12) (by trivial)]
            rewrite [Nat.mod_eq_of_lt (a := bv.toNat <<< 3)]
            all_goals simp [Nat.shiftLeft_eq]
            rewrite [←BitVec.toNat_mod_cancel_of_lt (x := bv) (m := 4) (by trivial)]
            simp
            omega
          rewrite [this, BitVec.setWidth_and]
          have : (bv_a &&& 1#3).toNat = (BitVec.setWidth 12 bv_a &&& 1#12).toNat := by simp
          rewrite [this]
          have :
            (BitVec.setWidth 12 bv_a &&& 1#12).toNat + ((BitVec.setWidth 12 bv_b &&& BitVec.setWidth 12 1#3) <<< 3).toNat < 2^4
          := by
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^12) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 64 = (BitVec.setWidth 12 (bv &&& 1#3) <<< 6).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 4096) (by omega)]
          rewrite [this]
          have :
            ((BitVec.setWidth 12 bv_a &&& 1#12) +
            (BitVec.setWidth 12 bv_b &&& BitVec.setWidth 12 1#3) <<< 3).toNat +
            (BitVec.setWidth 12 (bv_c &&& 1#3) <<< 6).toNat < 2^7
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 4096) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 4096) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^12) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 512 = (BitVec.setWidth 12 (bv &&& 1#3) <<< 9).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 4096) (by omega)]
          rewrite [this]
          have :
            ((BitVec.setWidth 12 bv_a &&& 1#12) +
            (BitVec.setWidth 12 bv_b &&& BitVec.setWidth 12 1#3) <<< 3 +
            BitVec.setWidth 12 (bv_c &&& 1#3) <<< 6).toNat +
            (BitVec.setWidth 12 (bv_d &&& 1#3) <<< 9).toNat < 2^10
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 4096) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 4096) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^12) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have : bv_a.toNat = (BitVec.setWidth 12 bv_a).toNat := by simp; rw [Nat.mod_eq_of_lt (by omega)]
          rewrite [this]
          have : bv_b.toNat * 8 = (BitVec.setWidth 12 bv_b <<< 3).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_c.toNat * 64 = (BitVec.setWidth 12 bv_c <<< 6).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_d.toNat * 512 = (BitVec.setWidth 12 bv_d <<< 9).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : (BitVec.setWidth 12 bv_a).toNat + (BitVec.setWidth 12 bv_b <<< 3).toNat < 2^6 := by omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^12) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have : (BitVec.setWidth 12 bv_a + BitVec.setWidth 12 bv_b <<< 3).toNat + (BitVec.setWidth 12 bv_c <<< 6).toNat < 2^12 := by
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
          have : (BitVec.setWidth 12 bv_a + BitVec.setWidth 12 bv_b <<< 3 + BitVec.setWidth 12 bv_c <<< 6).toNat + (BitVec.setWidth 12 bv_d <<< 9).toNat < 2^12 := by
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
            (BitVec.setWidth 12 bv_a + BitVec.setWidth 12 bv_b <<< 3 + BitVec.setWidth 12 bv_c <<< 6 + BitVec.setWidth 12 bv_d <<< 9).toNat =
            (BitVec.setWidth 192 (BitVec.setWidth 12 bv_a + BitVec.setWidth 12 bv_b <<< 3 + BitVec.setWidth 12 bv_c <<< 6 + BitVec.setWidth 12 bv_d <<< 9)).toNat
          := by
            simp
            symm
            apply Nat.mod_eq_of_lt
            omega
          rewrite [this, Normalize.normalize_unpacked_toNat]
          have :
            ((BitVec.setWidth 12 bv_a &&& 1#12) + (BitVec.setWidth 12 bv_b &&& BitVec.setWidth 12 1#3) <<< 3 + BitVec.setWidth 12 (bv_c &&& 1#3) <<< 6 + BitVec.setWidth 12 (bv_d &&& 1#3) <<< 9).toNat =
            (BitVec.setWidth 192 ((BitVec.setWidth 12 bv_a &&& 1#12) + (BitVec.setWidth 12 bv_b &&& BitVec.setWidth 12 1#3) <<< 3 + BitVec.setWidth 12 (bv_c &&& 1#3) <<< 6 + BitVec.setWidth 12 (bv_d &&& 1#3) <<< 9)).toNat
          := by
            simp
            symm
            apply Nat.mod_eq_of_lt
            omega
          rewrite [this, ←BitVec.toNat_eq, Normalize.mask_bitvec.eq_def]
          simp [keccak_constants]
          bv_decide
        . apply input_unrolled_lt_P <;> omega
      . apply output_lt_P
        . exact Nat.mod_lt _ (by trivial)
        . exact Nat.mod_lt _ (by trivial)
        . exact Nat.mod_lt _ (by trivial)
        . exact Nat.mod_lt _ (by trivial)
        . omega

end Keccak.Soundness.Lookups.Normalize_4

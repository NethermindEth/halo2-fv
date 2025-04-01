import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness.Lookups.Normalize_3
    lemma input_unrolled_lt_P (h_a: a < 3) (h_b: b < 3) (h_c: c < 3) (h_d: d < 3) (h_e: e < 3) (h_f: f < 3) (h_P: P > 74898): a + b * 8 + c * 64 + d*512 + e*4096 + f*32768 < P := by omega
    lemma input_range [NeZero P] (h_P: 8 < P) (h_row: row < 729): (Lookups.Normalize_3.input_by_row P row).val ≤ 74898 := by -- 2*(6 masked unpacked bits)
      unfold Lookups.Normalize_3.input_by_row
      simp [Lookups.Normalize_3.input_eval, keccak_constants, ZMod.val_add, ZMod.val_mul]
      apply le_trans (Nat.mod_le _ P)
      have : (8: ZMod P).val = 8 := by convert ZMod.val_cast_of_lt h_P
      have : Fact (1 < P) := by constructor; omega
      apply add_le_add (d := 65536)
      . apply add_le_add (d := 8192)
        . apply add_le_add (d := 1024)
          . apply add_le_add (d := 128)
            . apply add_le_add (d := 16)
              . omega
              . simp_all; omega
            . apply Nat.mul_le_mul (n₂ := 2) (m₂ := 64)
              . omega
              . convert ZMod.val_pow_le <;> simp_all
          . apply Nat.mul_le_mul (n₂ := 2) (m₂ := 512)
            . omega
            . convert ZMod.val_pow_le <;> simp_all
        . apply Nat.mul_le_mul (n₂ := 2) (m₂ := 4096)
          . omega
          . convert ZMod.val_pow_le <;> simp_all
      . apply Nat.mul_le_mul (n₂ := 2) (m₂ := 32768)
        . omega
        . convert ZMod.val_pow_le <;> simp_all
    lemma output_lt_P (h_a: a < 2) (h_b: b < 2) (h_c: c < 2) (h_d: d < 2) (h_e: e < 2) (h_f: f < 2) (h_P: P > 37449): a + b * 8 + c * 64 + d*512 + e*4096 + f*32768 < P := by omega
    lemma output_eq_normalized_input [NeZero P] (h_row: row < 729) (h_P: P ≥ 74899):
      (Lookups.Normalize_3.output_by_row P row).val = Normalize.normalize_unpacked (Lookups.Normalize_3.input_by_row P row |>.val) 6
    := by
      unfold Lookups.Normalize_3.input_by_row Lookups.Normalize_3.output_by_row Lookups.Normalize_3.input Lookups.Normalize_3.output
      simp [keccak_constants, ZMod.val_add, ZMod.val_mul]
      simp [
        OfNat.ofNat,
        Nat.mod_eq_of_lt (a := 8) (b := P) (by omega),
        Nat.mod_eq_of_lt (a := 64) (b := P) (by omega),
        Nat.mod_eq_of_lt (a := 512) (b := P) (by omega),
        Nat.mod_eq_of_lt (a := 4096) (b := P) (by omega),
        Nat.mod_eq_of_lt (a := 32768) (b := P) (by omega),
      ]
      set a := row / 243
      have h_a: a < 3 := by omega
      set b := row / 81 % 3
      have h_b: b < 3 := by omega
      set c := row / 27 % 3
      have h_c: c < 3 := by omega
      set d := row / 9 % 3
      have h_d: d < 3 := by omega
      set e := row / 3 % 3
      have h_e: e < 3 := by omega
      set f := row % 3
      have h_f: f < 3 := by omega
      rewrite [Nat.mod_eq_of_lt]
      . rewrite [Nat.mod_eq_of_lt (b := P)]
        . set bv_a := BitVec.ofNat 3 a
          set bv_b := BitVec.ofNat 3 b
          set bv_c := BitVec.ofNat 3 c
          set bv_d := BitVec.ofNat 3 d
          set bv_e := BitVec.ofNat 3 e
          set bv_f := BitVec.ofNat 3 f
          have : a = bv_a.toNat := by unfold bv_a; simp; rw [Nat.mod_eq_of_lt]; omega
          have : b = bv_b.toNat := by unfold bv_b; simp; rw [Nat.mod_eq_of_lt]; omega
          have : c = bv_c.toNat := by unfold bv_c; simp; rw [Nat.mod_eq_of_lt]; omega
          have : d = bv_d.toNat := by unfold bv_d; simp; rw [Nat.mod_eq_of_lt]; omega
          have : e = bv_e.toNat := by unfold bv_e; simp; rw [Nat.mod_eq_of_lt]; omega
          have : f = bv_f.toNat := by unfold bv_f; simp; rw [Nat.mod_eq_of_lt]; omega
          simp_all [←Nat.and_one_is_mod]
          have {bv: BitVec 3}: bv.toNat &&& 1 = (bv &&& 1#3).toNat := by simp
          rewrite [this, this, this, this, this, this]
          have {bv: BitVec 3}: bv.toNat * 8 = (BitVec.setWidth 18 bv <<< 3).toNat := by
            simp
            rewrite [BitVec.toNat_mod_cancel_of_lt (x := bv) (m := 18) (by trivial)]
            rewrite [Nat.mod_eq_of_lt (a := bv.toNat <<< 3)]
            all_goals simp [Nat.shiftLeft_eq]
            rewrite [←BitVec.toNat_mod_cancel_of_lt (x := bv) (m := 4) (by trivial)]
            simp
            omega
          rewrite [this, BitVec.setWidth_and]
          have : (bv_a &&& 1#3).toNat = (BitVec.setWidth 18 bv_a &&& 1#18).toNat := by simp
          rewrite [this]
          have :
            (BitVec.setWidth 18 bv_a &&& 1#18).toNat + ((BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3).toNat < 2^4
          := by
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^18) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 64 = (BitVec.setWidth 18 (bv &&& 1#3) <<< 6).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 262144) (by omega)]
          rewrite [this]
          have :
            ((BitVec.setWidth 18 bv_a &&& 1#18) +
            (BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3).toNat +
            (BitVec.setWidth 18 (bv_c &&& 1#3) <<< 6).toNat < 2^7
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^18) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 512 = (BitVec.setWidth 18 (bv &&& 1#3) <<< 9).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 262144) (by omega)]
          rewrite [this]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 4096 = (BitVec.setWidth 18 (bv &&& 1#3) <<< 12).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 262144) (by omega)]
          rewrite [this]
          have {bv: BitVec 3}: (bv &&& 1#3).toNat * 32768 = (BitVec.setWidth 18 (bv &&& 1#3) <<< 15).toNat := by
            simp [Nat.shiftLeft_eq]
            rw [Nat.mod_eq_of_lt (b := 262144) (by omega)]
          rewrite [this]
          have :
            ((BitVec.setWidth 18 bv_a &&& 1#18) +
            (BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3 +
            BitVec.setWidth 18 (bv_c &&& 1#3) <<< 6).toNat +
            (BitVec.setWidth 18 (bv_d &&& 1#3) <<< 9).toNat < 2^10
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^18) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have :
            ((BitVec.setWidth 18 bv_a &&& 1#18) +
            (BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3 +
            BitVec.setWidth 18 (bv_c &&& 1#3) <<< 6 +
            BitVec.setWidth 18 (bv_d &&& 1#3) <<< 9).toNat +
            (BitVec.setWidth 18 (bv_e &&& 1#3) <<< 12).toNat < 2^13
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^18) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have :
            ((BitVec.setWidth 18 bv_a &&& 1#18) +
            (BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3 +
            BitVec.setWidth 18 (bv_c &&& 1#3) <<< 6 +
            BitVec.setWidth 18 (bv_d &&& 1#3) <<< 9 +
            BitVec.setWidth 18 (bv_e &&& 1#3) <<< 12).toNat +
            (BitVec.setWidth 18 (bv_f &&& 1#3) <<< 15).toNat < 2^16
          := by
            simp
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            rewrite [Nat.mod_eq_of_lt (b := 262144) (by omega)]
            simp [Nat.shiftLeft_eq]
            omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^18) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have : bv_a.toNat = (BitVec.setWidth 18 bv_a).toNat := by simp; rw [Nat.mod_eq_of_lt (by omega)]
          rewrite [this]
          have : bv_b.toNat * 8 = (BitVec.setWidth 18 bv_b <<< 3).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_c.toNat * 64 = (BitVec.setWidth 18 bv_c <<< 6).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_d.toNat * 512 = (BitVec.setWidth 18 bv_d <<< 9).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_e.toNat * 4096 = (BitVec.setWidth 18 bv_e <<< 12).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : bv_f.toNat * 32768 = (BitVec.setWidth 18 bv_f <<< 15).toNat := by
            simp; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq]
          rewrite [this]
          have : (BitVec.setWidth 18 bv_a).toNat + (BitVec.setWidth 18 bv_b <<< 3).toNat < 2^6 := by omega
          rewrite [←Nat.mod_eq_of_lt (b := 2^18) (lt_trans this (by omega)), ←BitVec.toNat_add]
          have : (BitVec.setWidth 18 bv_a + BitVec.setWidth 18 bv_b <<< 3).toNat + (BitVec.setWidth 18 bv_c <<< 6).toNat < 2^18 := by
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
          have : (BitVec.setWidth 18 bv_a + BitVec.setWidth 18 bv_b <<< 3 + BitVec.setWidth 18 bv_c <<< 6).toNat + (BitVec.setWidth 18 bv_d <<< 9).toNat < 2^18 := by
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
          have : (BitVec.setWidth 18 bv_a + BitVec.setWidth 18 bv_b <<< 3 + BitVec.setWidth 18 bv_c <<< 6 + BitVec.setWidth 18 bv_d <<< 9).toNat + (BitVec.setWidth 18 bv_e <<< 12).toNat < 2^18 := by
            simp
            rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
            . omega
            . omega
            . omega
            . omega
            . omega
            . omega
            . rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
              simp
              rewrite [←BitVec.toNat_mod_cancel]; omega; omega; omega
              rewrite [←BitVec.toNat_mod_cancel]; omega
          rewrite [←Nat.mod_eq_of_lt this, ←BitVec.toNat_add]
          have : (BitVec.setWidth 18 bv_a + BitVec.setWidth 18 bv_b <<< 3 + BitVec.setWidth 18 bv_c <<< 6 + BitVec.setWidth 18 bv_d <<< 9 + BitVec.setWidth 18 bv_e <<< 12).toNat + (BitVec.setWidth 18 bv_f <<< 15).toNat < 2^18 := by
            simp
            rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
            . omega
            . omega
            . omega
            . omega
            . omega
            . omega
            . omega
            . rewrite [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
              simp
              rewrite [←BitVec.toNat_mod_cancel]; omega; omega; omega; omega
              rewrite [←BitVec.toNat_mod_cancel]; omega
          rewrite [←Nat.mod_eq_of_lt this, ←BitVec.toNat_add]
          have :
            (BitVec.setWidth 18 bv_a + BitVec.setWidth 18 bv_b <<< 3 + BitVec.setWidth 18 bv_c <<< 6 + BitVec.setWidth 18 bv_d <<< 9 + BitVec.setWidth 18 bv_e <<< 12 + BitVec.setWidth 18 bv_f <<< 15).toNat =
            (BitVec.setWidth 192 (BitVec.setWidth 18 bv_a + BitVec.setWidth 18 bv_b <<< 3 + BitVec.setWidth 18 bv_c <<< 6 + BitVec.setWidth 18 bv_d <<< 9 + BitVec.setWidth 18 bv_e <<< 12 + BitVec.setWidth 18 bv_f <<< 15)).toNat
          := by
            simp
            symm
            apply Nat.mod_eq_of_lt
            omega
          rewrite [this, Normalize.normalize_unpacked_toNat]
          have :
            ((BitVec.setWidth 18 bv_a &&& 1#18) + (BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3 + BitVec.setWidth 18 (bv_c &&& 1#3) <<< 6 + BitVec.setWidth 18 (bv_d &&& 1#3) <<< 9 + BitVec.setWidth 18 (bv_e &&& 1#3) <<< 12 + BitVec.setWidth 18 (bv_f &&& 1#3) <<< 15).toNat =
            (BitVec.setWidth 192 ((BitVec.setWidth 18 bv_a &&& 1#18) + (BitVec.setWidth 18 bv_b &&& BitVec.setWidth 18 1#3) <<< 3 + BitVec.setWidth 18 (bv_c &&& 1#3) <<< 6 + BitVec.setWidth 18 (bv_d &&& 1#3) <<< 9 + BitVec.setWidth 18 (bv_e &&& 1#3) <<< 12 + BitVec.setWidth 18 (bv_f &&& 1#3) <<< 15)).toNat
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
        . exact Nat.mod_lt _ (by trivial)
        . exact Nat.mod_lt _ (by trivial)
        . omega

end Keccak.Soundness.Lookups.Normalize_3

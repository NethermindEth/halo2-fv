import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Soundness.Attributes
import Examples.Scroll.Keccak.Spec.FinVals

namespace Keccak.Soundness

  -- def UInt64_to_unpacked_Nat (input: UInt64) :=
  --   List.range 64
  --   |>.map (λ x => (
  --     UInt64.ofNat 1 <<< UInt64.ofNat x,
  --     BitVec.ofNat 192 1 |>.shiftLeft (x*3))
  --   )
  --   |>.filter (λ ⟨x, _⟩ => x &&& input ≠ UInt64.ofNat 0)
  --   |>.foldr (λ ⟨_, val⟩ acc => val ||| acc) (BitVec.ofNat 192 0)
  --   |>.toNat

  def UInt64_to_unpacked_Nat (input: UInt64) :=
    List.range 64
    |>.map (λ i => (BitVec.setWidth 192 (input.toBitVec &&& (1#64<<<i))) <<< (i*2))
    |>.foldr (λ x acc => x ||| acc) 0#192
    |>.toNat

  lemma UInt64_to_unpacked_Nat_and :
    UInt64_to_unpacked_Nat (a &&& b) =
    (UInt64_to_unpacked_Nat a) &&& (UInt64_to_unpacked_Nat b)
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_and, ←BitVec.toNat_eq]
    simp [list_ops]
    bv_decide

  lemma UInt64_to_unpacked_Nat_xor:
    UInt64_to_unpacked_Nat (a ^^^ b) =
    (UInt64_to_unpacked_Nat a) ^^^ (UInt64_to_unpacked_Nat b)
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_xor, ←BitVec.toNat_eq]
    simp [list_ops]
    bv_decide

  lemma list_foldr_or_and {l: List (UInt64 × BitVec 192)} {f: UInt64 × BitVec 192 → BitVec 192} (h_init: init &&& mask = init):
    (List.foldr (λ x acc => f x ||| acc) init l) &&& mask = List.foldr (λ x acc => (f x ||| acc) &&& mask) init l
  := by
    induction l with
      | nil => simp_all
      | cons head tail h_step =>
        simp
        rewrite [BitVec.and_comm _ mask, BitVec.and_comm _ mask]
        rewrite [BitVec.and_comm _ mask] at h_step
        rewrite [←h_step]
        bv_decide

  lemma if_true_mask_else_self {cond} {mask y: BitVec 192} :
    (if cond = true then mask ||| y else y) = (if cond = true then mask else 0) ||| y := by
      by_cases cond
      . simp_all
      . simp_all

  lemma bitvec_rotate_zero (n: BitVec k):
    n.rotateLeft 0 = n
  := by
    simp [
      BitVec.rotateLeft_def,
      BitVec.ushiftRight_eq_zero
    ]


  lemma bitvec_if_and {cond} {n} {a b c: BitVec n} : ((if cond = true then a else b) &&& c) = (if cond = true then a &&& c else b &&& c) := by
      by_cases cond <;> simp_all

  lemma bitvec_and_or_distrib_right {n} {a b c: BitVec n}: (a ||| b) &&& c = ((a &&& c) ||| (b &&& c)) := by
      have := Nat.and_or_distrib_left c.toNat a.toNat b.toNat
      rewrite [
        Nat.and_comm,
        ←BitVec.toNat_or,
        ←BitVec.toNat_and,
        ←BitVec.toNat_and,
        ←BitVec.toNat_and,
        ←BitVec.toNat_or,
        ←BitVec.toNat_eq
      ] at this
      rw [this, BitVec.and_comm c a, BitVec.and_comm c b]

  lemma bitvec_ofNat_toNat_eq {n: ℕ} (x y: ℕ) (h: x = y) :
    (BitVec.ofNat x n).toNat = (BitVec.ofNat y n).toNat
  := by simp [h]

    lemma allOnes_toNat_mod_2pow (h_width: width > 192):
    (BitVec.allOnes width).toNat % (2^192) = (BitVec.allOnes 192).toNat
  := by
    rewrite [BitVec.toNat_allOnes, BitVec.toNat_allOnes]
    set x := 192; clear_value x
    rewrite [show width = x + (width-x) by omega]
    set extra := width-x
    rewrite [Nat.pow_add]
    have : extra > 0 := by omega
    have : 2 ^ extra > 0 := by simp_all
    have : 2^extra = (2^extra-1)+1 := by omega
    rewrite [this, mul_add, mul_one]
    rewrite [Nat.add_sub_assoc (by simp [Nat.one_le_pow])]
    rewrite [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    exact Nat.self_sub_mod (2 ^ x) 1

  lemma bitvec_setWidth_toNat (bv: BitVec width1) (h_width: width1 ≤ width2):
    (BitVec.setWidth width2 bv).toNat = bv.toNat
  := by
    simp
    rw [Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le
      (show bv.toNat < 2^ width1 by omega)
      (Nat.pow_le_pow_right (by trivial) h_width)

  lemma bitvec_toNat_shift (bv: BitVec width):
    bv.toNat <<< shift < 2^(width+shift)
  := by
    rewrite [Nat.shiftLeft_eq, pow_add, Nat.mul_lt_mul_right]
    . omega
    . exact Nat.two_pow_pos shift

  lemma bitvec_setWidth_shift_toNat {bv: BitVec width1} (h: width1 + shift ≤ width2):
    (BitVec.setWidth width2 bv <<< shift).toNat = bv.toNat <<< shift
  := by
    rw [
      BitVec.toNat_shiftLeft,
      bitvec_setWidth_toNat bv (by omega),
      Nat.mod_eq_of_lt
    ]
    exact lt_of_lt_of_le
      (bitvec_toNat_shift bv)
      (Nat.pow_le_pow_right (by trivial) h)

  lemma bitvec_toNat_shift_add (width2: ℕ) (bv1 : BitVec k) (bv2: BitVec width1) (h: k + width1 ≤ width2):
    bv1.toNat <<< width1 + bv2.toNat =
    (BitVec.setWidth width2 bv1 <<< width1 + BitVec.setWidth width2 bv2).toNat
  := by
    rw [
      BitVec.toNat_add,
      bitvec_setWidth_shift_toNat (by assumption),
      bitvec_setWidth_toNat _ (by omega),
      Nat.mod_eq_of_lt
    ]
    . rewrite [Nat.shiftLeft_eq]
      have h_bv1 : bv1.toNat ≤ 2^k - 1 := Nat.le_sub_one_of_lt (BitVec.isLt bv1)
      have h_bv2 : bv2.toNat ≤ 2^width1 - 1 := Nat.le_sub_one_of_lt (BitVec.isLt bv2)
      have h_bv1: bv1.toNat * (2^width1) ≤ (2^k-1)*(2^width1) := Nat.mul_le_mul_right (2 ^ width1) h_bv1
      rewrite [Nat.sub_mul, ←pow_add, one_mul] at h_bv1
      have h_width: 2^(k+width1) ≤ 2^width2 := by exact Nat.pow_le_pow_right (by trivial) h
      have h_add := Nat.add_le_add h_bv1 h_bv2
      have : 2 ^ (k+width1) - 2^width1 + (2^width1 - 1) = 2^(k+width1) - 1 := by
        rw [
          ←Nat.sub_add_comm, ←Nat.add_sub_assoc, Nat.sub_right_comm, Nat.add_sub_assoc,
          Nat.sub_self, add_zero
        ]
        . exact Nat.le_refl (2 ^ width1)
        . exact Nat.one_le_two_pow
        . exact Nat.pow_le_pow_right (by trivial) (by exact Nat.le_add_left width1 k)
      rewrite [this] at h_add
      rewrite [Nat.le_sub_one_iff_lt] at h_add
      . exact lt_of_lt_of_le h_add h_width
      . exact Nat.two_pow_pos (k + width1)

  lemma bitvec_12_toNat_shift_add (width2: ℕ) (bv1 : BitVec 12) (bv2: BitVec width1) (h: 12 + width1 ≤ width2):
    bv1.toNat <<< width1 + bv2.toNat =
    (BitVec.setWidth width2 bv1 <<< width1 + BitVec.setWidth width2 bv2).toNat
  := by
    rw [
      BitVec.toNat_add,
      bitvec_setWidth_shift_toNat (by assumption),
      bitvec_setWidth_toNat _ (by omega),
      Nat.mod_eq_of_lt
    ]
    . rewrite [Nat.shiftLeft_eq]
      have h_bv1 : bv1.toNat ≤ 2^12 - 1 := Nat.le_sub_one_of_lt (BitVec.isLt bv1)
      have h_bv2 : bv2.toNat ≤ 2^width1 - 1 := Nat.le_sub_one_of_lt (BitVec.isLt bv2)
      have h_bv1: bv1.toNat * (2^width1) ≤ (2^12-1)*(2^width1) := Nat.mul_le_mul_right (2 ^ width1) h_bv1
      rewrite [Nat.sub_mul, ←pow_add, one_mul] at h_bv1
      have h_width: 2^(12+width1) ≤ 2^width2 := by exact Nat.pow_le_pow_right (by trivial) h
      have h_add := Nat.add_le_add h_bv1 h_bv2
      have : 2 ^ (12+width1) - 2^width1 + (2^width1 - 1) = 2^(12+width1) - 1 := by
        rw [
          ←Nat.sub_add_comm, ←Nat.add_sub_assoc, Nat.sub_right_comm, Nat.add_sub_assoc,
          Nat.sub_self, add_zero
        ]
        . exact Nat.le_refl (2 ^ width1)
        . exact Nat.one_le_two_pow
        . exact Nat.pow_le_pow_right (by trivial) (by exact Nat.le_add_left width1 12)
      rewrite [this] at h_add
      rewrite [Nat.le_sub_one_iff_lt] at h_add
      . exact lt_of_lt_of_le h_add h_width
      . exact Nat.two_pow_pos (12 + width1)

  lemma bitvec_18_toNat_shift_add (width2: ℕ) (bv1 : BitVec 18) (bv2: BitVec width1) (h: 18 + width1 ≤ width2):
    bv1.toNat <<< width1 + bv2.toNat =
    (BitVec.setWidth width2 bv1 <<< width1 + BitVec.setWidth width2 bv2).toNat
  := by
    rw [
      BitVec.toNat_add,
      bitvec_setWidth_shift_toNat (by assumption),
      bitvec_setWidth_toNat _ (by omega),
      Nat.mod_eq_of_lt
    ]
    . rewrite [Nat.shiftLeft_eq]
      have h_bv1 : bv1.toNat ≤ 2^18 - 1 := Nat.le_sub_one_of_lt (BitVec.isLt bv1)
      have h_bv2 : bv2.toNat ≤ 2^width1 - 1 := Nat.le_sub_one_of_lt (BitVec.isLt bv2)
      have h_bv1: bv1.toNat * (2^width1) ≤ (2^18-1)*(2^width1) := Nat.mul_le_mul_right (2 ^ width1) h_bv1
      rewrite [Nat.sub_mul, ←pow_add, one_mul] at h_bv1
      have h_width: 2^(18+width1) ≤ 2^width2 := by exact Nat.pow_le_pow_right (by trivial) h
      have h_add := Nat.add_le_add h_bv1 h_bv2
      have : 2 ^ (18+width1) - 2^width1 + (2^width1 - 1) = 2^(18+width1) - 1 := by
        rw [
          ←Nat.sub_add_comm, ←Nat.add_sub_assoc, Nat.sub_right_comm, Nat.add_sub_assoc,
          Nat.sub_self, add_zero
        ]
        . exact Nat.le_refl (2 ^ width1)
        . exact Nat.one_le_two_pow
        . exact Nat.pow_le_pow_right (by trivial) (by exact Nat.le_add_left width1 18)
      rewrite [this] at h_add
      rewrite [Nat.le_sub_one_iff_lt] at h_add
      . exact lt_of_lt_of_le h_add h_width
      . exact Nat.two_pow_pos (18 + width1)

  lemma array_extract_5 {a: Array α} (h: a.size ≥ x+5): Array.extract a x (x+5) = #[a[x], a[x+1], a[x+2], a[x+3], a[x+4]] := by
    apply Array.ext
    . simp_all
    . intro i h_i1 h_i2
      match i with
        | 0 | 1 | 2 | 3 | 4 => simp
        | _+5 => exfalso; simp_all

  lemma array_foldl_xor_5 {a0: UInt64}: Array.foldl1 (fun x1 x2 ↦ x1 ^^^ x2) #[a0, a1, a2, a3, a4] = a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 := by
    aesop

  lemma array_range_5: Array.range 5 = #[0,1,2,3,4] := by rfl
  lemma array_range_25: Array.range 25 = #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24] := by rfl

  def state_get (state: LeanCrypto.HashFunctions.SHA3SR) (h_state: state.size ≥ 25) (x y: Fin 5): UInt64 :=
    state[(5: ℕ)*↑y+↑x]

  def s_equiv (s: Fin 5 → Fin 5 → ZMod P) (state: LeanCrypto.HashFunctions.SHA3SR) (h_state: state.size ≥ 25): Prop :=
    ∀ x y: Fin 5, (s y x).val = UInt64_to_unpacked_Nat (state_get state h_state x y)

  @[zmod_pow_shift_simps] lemma zmod_pow_12_mul {x: ℕ}: (2: ZMod P) ^ 12 * ↑x = Nat.cast ((2: ℕ)^12 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_18_mul {x: ℕ}: (2: ZMod P) ^ 18 * ↑x = Nat.cast ((2: ℕ)^18 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_24_mul {x: ℕ}: (2: ZMod P) ^ 24 * ↑x = Nat.cast ((2: ℕ)^24 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_32_mul {x: ℕ}: (2: ZMod P) ^ 32 * ↑x = Nat.cast ((2: ℕ)^32 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_36_mul {x: ℕ}: (2: ZMod P) ^ 36 * ↑x = Nat.cast ((2: ℕ)^36 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_48_mul {x: ℕ}: (2: ZMod P) ^ 48 * ↑x = Nat.cast ((2: ℕ)^48 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_54_mul {x: ℕ}: (2: ZMod P) ^ 54 * ↑x = Nat.cast ((2: ℕ)^54 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_60_mul {x: ℕ}: (2: ZMod P) ^ 60 * ↑x = Nat.cast ((2: ℕ)^60 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_72_mul {x: ℕ}: (2: ZMod P) ^ 72 * ↑x = Nat.cast ((2: ℕ)^72 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_84_mul {x: ℕ}: (2: ZMod P) ^ 84 * ↑x = Nat.cast ((2: ℕ)^84 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_90_mul {x: ℕ}: (2: ZMod P) ^ 90 * ↑x = Nat.cast ((2: ℕ)^90 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_96_mul {x: ℕ}: (2: ZMod P) ^ 96 * ↑x = Nat.cast ((2: ℕ)^96 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_108_mul {x: ℕ}: (2: ZMod P) ^ 108 * ↑x = Nat.cast ((2: ℕ)^108 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_120_mul {x: ℕ}: (2: ZMod P) ^ 120 * ↑x = Nat.cast ((2: ℕ)^120 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_126_mul {x: ℕ}: (2: ZMod P) ^ 126 * ↑x = Nat.cast ((2: ℕ)^126 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_132_mul {x: ℕ}: (2: ZMod P) ^ 132 * ↑x = Nat.cast ((2: ℕ)^132 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_144_mul {x: ℕ}: (2: ZMod P) ^ 144 * ↑x = Nat.cast ((2: ℕ)^144 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_156_mul {x: ℕ}: (2: ZMod P) ^ 156 * ↑x = Nat.cast ((2: ℕ)^156 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_162_mul {x: ℕ}: (2: ZMod P) ^ 162 * ↑x = Nat.cast ((2: ℕ)^162 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_168_mul {x: ℕ}: (2: ZMod P) ^ 168 * ↑x = Nat.cast ((2: ℕ)^168 * x) := by simp [zmod_pow_simps]
  @[zmod_pow_shift_simps] lemma zmod_pow_180_mul {x: ℕ}: (2: ZMod P) ^ 180 * ↑x = Nat.cast ((2: ℕ)^180 * x) := by simp [zmod_pow_simps]

end Keccak.Soundness

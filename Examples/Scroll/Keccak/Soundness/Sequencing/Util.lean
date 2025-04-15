import Examples.Scroll.Keccak.Soundness.Sequencing.Iota
import Examples.Scroll.Keccak.Soundness.Iota
import Examples.Scroll.Keccak.Soundness.Rho
import Examples.Scroll.Keccak.Soundness.Theta

namespace Keccak.Soundness

  lemma congr_xor {a b c d: ℕ} (h_left: a=c) (h_right: b=d):
    a^^^b = c^^^d
  := by simp_all

  lemma fold_or_accumulator{list: List T} {f: T → BitVec 192} :
    List.foldr (λ x acc => (f x) ||| acc) init list =
    (List.foldr (λ x acc => (f x) ||| acc) 0#192 list) ||| init
  := by
    induction list with
      | nil => simp
      | cons head tail h_step =>
        unfold List.foldr
        rw [h_step, BitVec.or_assoc]

  lemma uint64_shift_and_xor:
    1 <<< UInt64.ofNat n &&& (a ^^^ b) =
    (1 <<< UInt64.ofNat n &&& a) ^^^
    (1 <<< UInt64.ofNat n &&& b)
  := by
    apply UInt64.eq_of_toBitVec_eq
    simp
    bv_decide

  lemma uint64_zero_xor:
    (0: UInt64) ^^^ x = x
  := by
    apply UInt64.eq_of_toBitVec_eq
    simp

  lemma uint64_lt_2_pow_192:
    UInt64_to_unpacked_Nat x < 2^192
  := by
    rewrite [←Normalize.normalize_unpacked_UInt64]
    apply lt_of_le_of_lt
    . exact Normalize.normalize_unpacked_64_le_mask
    . decide

  lemma bitvec_ofNat_uint64_toNat (x: UInt64):
    (BitVec.ofNat 64 x.toNat) = x.toBitVec
  := by
      unfold UInt64.toNat
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

  lemma rotate_to_unpacked_nat_0:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 0) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT * 0)).toNat
  := by
    unfold LeanCrypto.rotateL
    simp only [keccak_constants, Nat.reduceMul, bitvec_rotate_zero]
    unfold UInt64_to_unpacked_Nat
    simp

  lemma rotate_to_unpacked_nat_1:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 1) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft BIT_COUNT).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_2:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 2) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*2)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_3:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 3) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*3)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_6:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 6) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*6)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_8:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 8) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*8)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_10:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 10) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*10)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_14:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 14) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*14)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_15:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 15) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*15)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_18:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 18) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*18)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_20:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 20) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*20)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_21:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 21) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*21)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_25:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 25) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*25)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_27:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 27) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*27)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_28:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 28) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*28)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_36:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 36) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*36)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_39:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 39) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*39)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_41:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 41) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*41)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_43:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 43) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*43)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_44:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 44) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*44)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_45:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 45) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*45)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_55:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 55) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*55)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_56:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 56) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*56)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_61:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 61) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*61)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_to_unpacked_nat_62:
    UInt64_to_unpacked_Nat (LeanCrypto.rotateL x 62) =
    ((BitVec.ofNat 192 (UInt64_to_unpacked_Nat x)).rotateLeft (BIT_COUNT*62)).toNat
  := by
    unfold UInt64_to_unpacked_Nat
    rewrite [←BitVec.toNat_eq]
    simp only [keccak_constants, LeanCrypto.rotateL]
    have (x: ℕ): (UInt64.ofNat x).toBitVec = BitVec.ofNat 64 x := by rfl
    rewrite [this, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    clear this
    rewrite [bitvec_ofNat_uint64_toNat]
    simp only [
      list_ops,
      List.map_cons,
      List.map_nil,
      BitVec.ofNat_toNat,
      BitVec.setWidth_eq,
      Nat.reduceMul
    ]
    bv_decide

  lemma rotate_normalized_0:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 0).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 0).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_3:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 3).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 3).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_uint64_xors_normalized_3:
    Normalize.normalize_unpacked
      ((BitVec.ofNat 192 (
        (UInt64_to_unpacked_Nat x1 ^^^
          (UInt64_to_unpacked_Nat x2 ^^^
            (UInt64_to_unpacked_Nat x3 ^^^
              (UInt64_to_unpacked_Nat x4 ^^^
                UInt64_to_unpacked_Nat x5)))))
      ).rotateLeft 3).toNat
      64 =
    ((BitVec.ofNat 192 (
        (UInt64_to_unpacked_Nat x1 ^^^
          (UInt64_to_unpacked_Nat x2 ^^^
            (UInt64_to_unpacked_Nat x3 ^^^
              (UInt64_to_unpacked_Nat x4 ^^^
                UInt64_to_unpacked_Nat x5)))))
      ).rotateLeft 3).toNat
  := by
    rewrite [
      ←Normalize.normalize_unpacked_UInt64 (x := x1),
      ←Normalize.normalize_unpacked_UInt64 (x := x2),
      ←Normalize.normalize_unpacked_UInt64 (x := x3),
      ←Normalize.normalize_unpacked_UInt64 (x := x4),
      ←Normalize.normalize_unpacked_UInt64 (x := x5),
    ]
    simp only [←Normalize.normalize_unpacked_xor]
    rw [rotate_normalized_3, Normalize.normalize_unpacked_idempotent]

  lemma rotate_normalized_6:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 6).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 6).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_9:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 9).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 9).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_18:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 18).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 18).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_24:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 24).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 24).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_30:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 30).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 30).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_42:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 42).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 42).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_45:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 45).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 45).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_54:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 54).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 54).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_60:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 60).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 60).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_63:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 63).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 63).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_75:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 75).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 75).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_81:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 81).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 81).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_84:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 84).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 84).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_108:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 108).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 108).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_117:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 117).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 117).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_123:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 123).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 123).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_129:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 129).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 129).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_132:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 132).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 132).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_135:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 135).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 135).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_165:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 165).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 165).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_168:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 168).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 168).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_183:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 183).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 183).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma rotate_normalized_186:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft 186).toNat =
    Normalize.normalize_unpacked ((BitVec.ofNat 192 x).rotateLeft 186).toNat 64
  := by
    rewrite [
      Normalize.normalize_unpacked_toNat,
      BitVec.and_assoc
    ]
    rewrite [Normalize.normalize_unpacked_to_bitvec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simp only [
      keccak_constants, Nat.reduceMul, BitVec.setWidth_eq,
      BitVec.and_allOnes, Normalize.mask_bitvec_ofNat, ←BitVec.toNat_eq,
      Normalize.mask_bitvec.eq_def
    ]
    bv_decide

  lemma normalize_add_add_eq_xor:
    Normalize.normalize_unpacked (
      Normalize.normalize_unpacked x1 64 +
      Normalize.normalize_unpacked x2 64 +
      Normalize.normalize_unpacked x3 64
    ) 64 =
    Normalize.normalize_unpacked (
      Normalize.normalize_unpacked x1 64 ^^^
      Normalize.normalize_unpacked x2 64 ^^^
      Normalize.normalize_unpacked x3 64
    ) 64
  := by
    simp only [
      Normalize.normalize_unpacked_to_bitvec, keccak_constants, Nat.reduceMul,
    ]
    rewrite [←BitVec.toNat_add_of_lt, ←BitVec.toNat_add_of_lt]
    . simp only [
        ←BitVec.toNat_eq, ←BitVec.toNat_xor, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        Normalize.mask_bitvec_ofNat, Normalize.mask_bitvec.eq_def
      ]
      bv_decide
    . simp [Normalize.mask, Nat.and_assoc]
      exact lt_of_le_of_lt
        (add_le_add
          (le_trans
            (Nat.mod_le _ _)
            (add_le_add
              Nat.and_le_right
              Nat.and_le_right))
          Nat.and_le_right)
        (by trivial)
    . simp [Normalize.mask, Nat.and_assoc]
      exact lt_of_le_of_lt
        (add_le_add Nat.and_le_right Nat.and_le_right)
        (by trivial)

  lemma normalize_add_add_add_add_eq_xor:
    Normalize.normalize_unpacked (
      Normalize.normalize_unpacked x1 64 +
      Normalize.normalize_unpacked x2 64 +
      Normalize.normalize_unpacked x3 64 +
      Normalize.normalize_unpacked x4 64 +
      Normalize.normalize_unpacked x5 64
    ) 64 =
    Normalize.normalize_unpacked (
      Normalize.normalize_unpacked x1 64 ^^^
      Normalize.normalize_unpacked x2 64 ^^^
      Normalize.normalize_unpacked x3 64 ^^^
      Normalize.normalize_unpacked x4 64 ^^^
      Normalize.normalize_unpacked x5 64
    ) 64
  := by
    simp only [
      Normalize.normalize_unpacked_to_bitvec, keccak_constants, Nat.reduceMul,
      add_assoc
    ]
    rewrite [←BitVec.toNat_add_of_lt, ←BitVec.toNat_add_of_lt, ←BitVec.toNat_add_of_lt, ←BitVec.toNat_add_of_lt]
    . simp only [
        ←BitVec.toNat_eq, ←BitVec.toNat_xor, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        Normalize.mask_bitvec_ofNat, Normalize.mask_bitvec.eq_def
      ]
      bv_decide
    . simp [Normalize.mask, Nat.and_assoc]
      exact lt_of_le_of_lt
        (add_le_add
          Nat.and_le_right
          (le_trans
            (Nat.mod_le _ _)
            (add_le_add
              Nat.and_le_right
              (add_le_add
                Nat.and_le_right
                (add_le_add Nat.and_le_right Nat.and_le_right)
              )
            )
          )
        )
        (by trivial)
    . simp [Normalize.mask, Nat.and_assoc]
      exact lt_of_le_of_lt
        (add_le_add
          Nat.and_le_right
          (le_trans
            (Nat.mod_le _ _)
            (add_le_add
              Nat.and_le_right
              (add_le_add Nat.and_le_right Nat.and_le_right)
            )
          )
        )
        (by trivial)
    . simp [Normalize.mask, Nat.and_assoc]
      exact lt_of_le_of_lt
        (add_le_add
          Nat.and_le_right
          (le_trans
            (Nat.mod_le _ _)
            (add_le_add
              Nat.and_le_right
              Nat.and_le_right
            )
          )
        )
        (by trivial)
    . simp [Normalize.mask, Nat.and_assoc, lt_of_le_of_lt, add_le_add, Nat.and_le_right]
      exact lt_of_le_of_lt
        (add_le_add Nat.and_le_right Nat.and_le_right)
        (by trivial)

  lemma normalize_uint64_add_add_add_add_eq_xor:
    Normalize.normalize_unpacked (
      UInt64_to_unpacked_Nat x1 +
      UInt64_to_unpacked_Nat x2 +
      UInt64_to_unpacked_Nat x3 +
      UInt64_to_unpacked_Nat x4 +
      UInt64_to_unpacked_Nat x5
    ) 64 =
    Normalize.normalize_unpacked (
      UInt64_to_unpacked_Nat x1 ^^^
      UInt64_to_unpacked_Nat x2 ^^^
      UInt64_to_unpacked_Nat x3 ^^^
      UInt64_to_unpacked_Nat x4 ^^^
      UInt64_to_unpacked_Nat x5
    ) 64
  := by
    convert normalize_add_add_add_add_eq_xor
    all_goals rw [←Normalize.normalize_unpacked_UInt64]
    all_goals rw [Normalize.normalize_unpacked_idempotent]

  lemma uint64_ofNat_bitvec_toNat (bv: BitVec 64) : UInt64.ofNat bv.toNat = UInt64.ofBitVec bv := by
    unfold UInt64.ofNat
    simp

  lemma uint64_to_unpacked_nat_complement:
    UInt64_to_unpacked_Nat (LeanCrypto.complement x) =
    Normalize.normalize_unpacked (bit_invert (UInt64_to_unpacked_Nat x) 64) 64
  := by
    unfold LeanCrypto.complement
    rewrite [
      bitvec_ofNat_uint64_toNat,
      uint64_ofNat_bitvec_toNat,
      Normalize.normalize_unpacked_to_bitvec,
      bit_invert.eq_def,
      BitVec.ofNat_toNat,
      BitVec.and_assoc,
    ]
    simp only [keccak_constants, Nat.reduceMul, BitVec.setWidth_eq, BitVec.and_allOnes]
    unfold UInt64_to_unpacked_Nat
    simp only [
      list_ops,
      List.map_nil,
      List.map_cons,
      Nat.reduceMul,
      BitVec.ofNat_toNat,
      ←BitVec.toNat_eq,
      Normalize.mask.eq_def
    ]
    bv_decide





end Keccak.Soundness

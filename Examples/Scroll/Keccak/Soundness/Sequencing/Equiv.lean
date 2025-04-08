import Examples.Scroll.Keccak.Soundness.Sequencing.Iota
import Examples.Scroll.Keccak.Soundness.Iota

namespace Keccak.Soundness

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

  lemma UInt64_to_unpacked_Nat_xor:
    UInt64_to_unpacked_Nat (a ^^^ b) =
    (UInt64_to_unpacked_Nat a) ^^^ (UInt64_to_unpacked_Nat b)
  := by
    have :
      (BitVec.ofNat 192 (UInt64_to_unpacked_Nat (a ^^^ b))).toNat =
      (BitVec.ofNat 192 ((UInt64_to_unpacked_Nat a) ^^^ (UInt64_to_unpacked_Nat b))).toNat
    := by
      rewrite [←BitVec.toNat_eq]
      apply BitVec.eq_of_getElem_eq
      intro i h_i

      done
    simp at this
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at this
    . exact this
    . rewrite [
        ←Normalize.normalize_unpacked_UInt64 (x := a),
        ←Normalize.normalize_unpacked_UInt64 (x := b),
        ←Normalize.normalize_unpacked_xor
      ]
      apply lt_of_le_of_lt
      . exact Normalize.normalize_unpacked_64_le_mask
      . decide
    . exact uint64_lt_2_pow_192


    -- unfold UInt64_to_unpacked_Nat
    -- unfold List.foldr
    -- rewrite [List.range_succ_eq_map]
    -- rewrite [List.map_cons, List.filter_cons]
    -- dsimp only
    -- rewrite [show UInt64.ofNat 1 = (1: UInt64) by rfl, uint64_shift_and_xor]
    -- simp [List.filter_cons]




    -- generalize 64 = l
    -- induction l with
    --   | zero => simp
    --   | succ l h_l =>
    --     simp_all [List.range_succ]
    --     rewrite [←BitVec.toNat_xor, ←BitVec.toNat_eq] at h_l
    --     rewrite [
    --       fold_or_accumulator,
    --       fold_or_accumulator (init := List.foldr _ _ _),
    --       fold_or_accumulator (init := List.foldr _ _ _),
    --       h_l,
    --       ←BitVec.toNat_xor,
    --       ←BitVec.toNat_eq,
    --     ]
    --     simp [List.filter_cons, List.filter_nil]
    --     rewrite [uint64_shift_and_xor]
    --     by_cases h_a: 1 <<< UInt64.ofNat l &&& a = 0
    --     <;> by_cases h_b: 1 <<< UInt64.ofNat l &&& b = 0
    --     . simp_all [uint64_zero_xor]
    --     . simp_all [uint64_zero_xor]



  lemma iota_s_equiv {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c)(h_round: round ∈ Finset.Icc 0 23) (h_P: 2^200 ≤ P) (h_state: state = #[x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24]):
    .some (iota_s c (round+1) 0 0).val =
    (LeanCrypto.HashFunctions.keccak_round round state)[0]?.map UInt64_to_unpacked_Nat
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round': (round+1) ∈ Finset.Icc 1 24 := by
      apply Finset.mem_Icc.mpr
      apply Finset.mem_Icc.mp at h_round
      omega
    simp [
      LeanCrypto.HashFunctions.keccak_round,
      spec_iota_0 h_state,
      iota_s_roundConstant h_meets_constraints (by omega) h_round',
      ZMod.val_add,
      UInt64_to_unpacked_Nat_xor
    ]

end Keccak.Soundness

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness.Lookups
  namespace ChiBase
    lemma output_range [NeZero P] (h_P: 8 < P):
      (Lookups.ChiBase.output_by_row P row).val ≤ 585
    := by
      have : (8: ZMod P).val = 8 := by convert ZMod.val_cast_of_lt h_P
      simp [
        Lookups.ChiBase.output_by_row.eq_def, Lookups.ChiBase.output_eval, keccak_constants,
        ZMod.val_add, ZMod.val_mul, this
      ]
      have : Fact (1 < P) := by constructor; omega
      apply le_trans (Nat.mod_le _ _)
      apply add_le_add (d := 512)
      . apply add_le_add (d := 64)
        . apply add_le_add (d := 8)
          . aesop
          . aesop
        . apply Nat.mul_le_mul (n₂ := 1) (m₂ := 64)
          . aesop
          . convert ZMod.val_pow_le <;> simp_all
      . apply Nat.mul_le_mul (n₂ := 1) (m₂ := 512)
        . aesop
        . convert ZMod.val_pow_le <;> simp_all

    def chi_base_lookup (bv: BitVec 192) :=
      (bv &&& 1#192) ^^^ ((bv &&& 2#192) >>> 1)

    lemma chi_base_lookup_range (bv: BitVec 192): (chi_base_lookup bv).toNat ≤ 1 := by
      have : chi_base_lookup bv ≤ 1#192 := by
        unfold chi_base_lookup
        bv_decide
      bv_omega

    lemma chi_base_lookup_table_range (x: Fin 5): CHI_BASE_LOOKUP_TABLE x ≤ 1 := by
      unfold CHI_BASE_LOOKUP_TABLE
      match x with | 0 | 1 | 2 | 3 | 4 => decide

    lemma chi_base_lookup_bitvec (h: x = bv.toNat) (h_bv: bv < 5#192):
      CHI_BASE_LOOKUP_TABLE ⟨x, hx⟩ =
      (chi_base_lookup bv).toNat
    := by
      match bv with
        | 0#192 | 1#192 | 2#192 | 3#192 | 4#192 =>
          simp_all [chi_base_lookup.eq_def, CHI_BASE_LOOKUP_TABLE.eq_def]

    lemma chi_base_lookup_table_combine_to_bitvec
      (h_a: a < 5)
      (h_bv_a: bv_a < 5#192)
      (h_bv_a': a = bv_a.toNat)
      (h_b: b < 5)
      (h_bv_b: bv_b < 5#192)
      (h_bv_b': b = bv_b.toNat)
      (h_c: c < 5)
      (h_bv_c: bv_c < 5#192)
      (h_bv_c': c = bv_c.toNat)
      (h_d: d < 5)
      (h_bv_d: bv_d < 5#192)
      (h_bv_d': d = bv_d.toNat)
    :
      CHI_BASE_LOOKUP_TABLE ⟨a, h_a⟩ +
      CHI_BASE_LOOKUP_TABLE ⟨b, h_b⟩ * 8 +
      CHI_BASE_LOOKUP_TABLE ⟨c, h_c⟩ * 64 +
      CHI_BASE_LOOKUP_TABLE ⟨d, h_d⟩ * 512 =
      (chi_base_lookup bv_a +
      chi_base_lookup bv_b * 8#192 +
      chi_base_lookup bv_c * 64#192 +
      chi_base_lookup bv_d * 512#192).toNat
    := by
      have := chi_base_lookup_range bv_a;
      have := chi_base_lookup_range bv_b;
      have := chi_base_lookup_range bv_c;
      have := chi_base_lookup_range bv_d;
      rewrite [
        BitVec.toNat_add_of_lt,
        BitVec.toNat_add_of_lt,
        BitVec.toNat_add_of_lt,
        BitVec.toNat_mul_of_lt,
        BitVec.toNat_mul_of_lt,
        BitVec.toNat_mul_of_lt,
        chi_base_lookup_bitvec h_bv_a' h_bv_a,
        chi_base_lookup_bitvec h_bv_b' h_bv_b,
        chi_base_lookup_bitvec h_bv_c' h_bv_c,
        chi_base_lookup_bitvec h_bv_d' h_bv_d
      ] <;> simp <;> omega

    set_option maxHeartbeats 400000
    lemma output_eq_transformed_input {x0 x1 x2: ZMod P}
      (h_x0: x0 = Normalize.normalize_unpacked x0.val 4)
      (h_x1: x1 = Normalize.normalize_unpacked x1.val 4)
      (h_x2: x2 = Normalize.normalize_unpacked x2.val 4)
      (h_input: Scatter.expr 3 4 - 2 * x0 + x1 - x2 = Lookups.ChiBase.input_by_row P row)
      (h_P: P ≥ 2^(4*BIT_COUNT))
    :
      (Lookups.ChiBase.output_by_row P row).val =
      x0.val ^^^ (
        (0b111111111111 ^^^ x1.val) &&&
        x2.val
      )
    := by
      simp [keccak_constants] at h_P
      have : NeZero P := by constructor; omega
      have : Fact (1 < P) := by constructor; omega
      have h_3: (3: ZMod P).val = 3 := by
        convert ZMod.val_natCast 3
        rw [Nat.mod_eq_of_lt]; omega
      have h_8: (8: ZMod P).val = 8 := by
        convert ZMod.val_natCast 8
        rw [Nat.mod_eq_of_lt]; omega
      have h_8_2 := ZMod.val_pow (n := P) (m := 2) (a := 8)
      rewrite [h_8] at h_8_2
      specialize h_8_2 (by omega)
      have h_8_3 := ZMod.val_pow (n := P) (m := 3) (a := 8)
      rewrite [h_8] at h_8_3
      specialize h_8_3 (by omega)
      simp [
        Lookups.ChiBase.output_by_row.eq_def, Lookups.ChiBase.output_eval,
        keccak_constants, ZMod.val_mul, ZMod.val_add, h_8, h_8_2, h_8_3
      ]
      simp [
        Lookups.ChiBase.input_by_row.eq_def, Lookups.ChiBase.input_eval,
        keccak_constants
      ] at h_input
      set a := row / 125 % 5
      set b := row / 25 % 5
      set c := row / 5 % 5
      set d := row % 5
      have h_a: a < 5 := by omega
      have h_b: b < 5 := by omega
      have h_c: c < 5 := by omega
      have h_d: d < 5 := by omega
      unfold Nat.cast NatCast.natCast Fin.instNatCast Fin.ofNat'
      dsimp only
      simp [
        Nat.mod_eq_of_lt h_a,
        Nat.mod_eq_of_lt h_b,
        Nat.mod_eq_of_lt h_c,
        Nat.mod_eq_of_lt h_d
      ]
      have h_bv_x0: x0.val = (BitVec.ofNat 12 (x0.val)).toNat := by
        simp
        rw [Nat.mod_eq_of_lt]
        rewrite [h_x0]
        simp [Normalize.normalize_unpacked, keccak_constants]
        have := Nat.and_le_right (n :=  x0.val &&& Normalize.mask) (m := 4095)
        rewrite [Nat.mod_eq_of_lt] <;> omega
      have h_bv_x1: x1.val = (BitVec.ofNat 12 (x1.val)).toNat := by
        simp
        rw [Nat.mod_eq_of_lt]
        rewrite [h_x1]
        simp [Normalize.normalize_unpacked, keccak_constants]
        have := Nat.and_le_right (n :=  x1.val &&& Normalize.mask) (m := 4095)
        rewrite [Nat.mod_eq_of_lt] <;> omega
      have h_bv_x2: x2.val = (BitVec.ofNat 12 (x2.val)).toNat := by
        simp
        rw [Nat.mod_eq_of_lt]
        rewrite [h_x2]
        simp [Normalize.normalize_unpacked, keccak_constants]
        have := Nat.and_le_right (n :=  x2.val &&& Normalize.mask) (m := 4095)
        rewrite [Nat.mod_eq_of_lt] <;> omega
      have (a b: ZMod P) (h: a = b): a.val = b.val := by simp [*]
      apply this at h_input
      simp [
        sub_eq_add_neg,
        ZMod.val_add, ZMod.val_mul,
        h_8, h_8_2, h_8_3
      ] at h_input
      have h_neg (x: ZMod P): (-x).val = (P - x.val) % P := by
        by_cases h: x = 0
        . simp [h]
        . have : NeZero x := by constructor; simp [h]
          rw [ZMod.val_neg_of_ne_zero, Nat.mod_eq_of_lt]
          have : x.val ≠ 0 := by simp [h]
          omega
      rewrite [
        h_neg, h_neg, ZMod.val_mul, ZMod.val_two_eq_two_mod,
        Scatter.expr.eq_def, Lookups.PackTable.pack.eq_def,
        Lookups.PackTable.pack_with_base
      ] at h_input
      simp [
        keccak_constants, ZMod.val_add, ZMod.val_mul, h_8, h_3
      ] at h_input
      rewrite [
        Nat.add_mod,
      ] at h_input
      have h_x0_norm : x0.val = Normalize.normalize_unpacked x0.val 4 := by
        rewrite (occs := .pos [1]) [h_x0]
        simp
        rw [Nat.mod_eq_of_lt]
        apply Nat.lt_of_le_of_lt
        . exact Normalize.normalize_unpacked_4_le
        . omega
      have h_x1_norm : x1.val = Normalize.normalize_unpacked x1.val 4 := by
        rewrite (occs := .pos [1]) [h_x1]
        simp
        rw [Nat.mod_eq_of_lt]
        apply Nat.lt_of_le_of_lt
        . exact Normalize.normalize_unpacked_4_le
        . omega
      have h_x2_norm : x2.val = Normalize.normalize_unpacked x2.val 4 := by
        rewrite (occs := .pos [1]) [h_x2]
        simp
        rw [Nat.mod_eq_of_lt]
        apply Nat.lt_of_le_of_lt
        . exact Normalize.normalize_unpacked_4_le
        . omega
      have h_x0_range: x0.val ≤ 585 := by rewrite [h_x0_norm]; exact Normalize.normalize_unpacked_4_le
      have h_x1_range: x1.val ≤ 585 := by rewrite [h_x1_norm]; exact Normalize.normalize_unpacked_4_le
      have h_x2_range: x2.val ≤ 585 := by rewrite [h_x2_norm]; exact Normalize.normalize_unpacked_4_le
      have h_input:
        1755 - 2*x0.val + x1.val - x2.val =
        a + b*8 + c*64 + d*512
      := by
        by_cases h: x0.val = 0
        . simp [h] at h_input ⊢
          rewrite [Nat.add_mod] at h_input
          by_cases h: x2.val = 0
          . simp [h] at h_input ⊢
            rewrite [
              Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)
            ] at h_input
            exact h_input
          . rewrite [
              Nat.mod_eq_of_lt (a := P - x2.val) (by omega),
              Nat.mod_eq_of_lt (a := 1755 + x1.val) (by omega),
              Nat.mod_eq_of_lt (a := _ + d * 512) (by omega)
            ] at h_input
            rewrite [
              ←h_input,
              ←Nat.add_sub_assoc (by omega)
            ]
            have : 1755 + x1.val + P - x2.val = 1755 + x1.val - x2.val + P := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt]
            omega
        . rewrite [
            show 1755 % P + (P - 2 * x0.val % P) % P = 1755 - 2*x0.val + P by
              rewrite [
                Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt (a := 2*_) (by omega),
                Nat.mod_eq_of_lt (by omega)
              ]
              omega,
            add_assoc, add_comm (a := P), ←add_assoc, Nat.add_mod_right
          ] at h_input
          by_cases h: x2.val = 0
          . simp [h] at h_input ⊢
            rewrite [
              Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)
            ] at h_input
            exact h_input
          . rewrite [
              Nat.mod_eq_of_lt (a := _ + x1.val) (by omega),
              Nat.mod_eq_of_lt (a := _ - x2.val) (by omega),
              Nat.mod_eq_of_lt (a := _ + d * 512) (by omega)
            ] at h_input
            rewrite [
              ←h_input,
              ←Nat.add_sub_assoc (by omega)
            ]
            have : 1755 - 2*x0.val + x1.val + P - x2.val = 1755 - 2*x0.val + x1.val - x2.val + P := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt]
            omega
      rewrite [
        h_x0_norm, h_bv_x0,
        h_x1_norm, h_bv_x1,
        h_x2_norm, h_bv_x2,
        Normalize.normalize_unpacked_toNat_small (by trivial),
        Normalize.normalize_unpacked_toNat_small (by trivial),
        Normalize.normalize_unpacked_toNat_small (by trivial),
        show 4095 = (BitVec.ofNat 192 4095).toNat by decide,
        ←BitVec.toNat_xor,
        ←BitVec.toNat_and,
        ←BitVec.toNat_xor,
        Nat.mod_eq_of_lt
      ]
      . simp only [keccak_constants, Nat.reduceMul, Normalize.mask_bitvec.eq_def]
        rewrite [
          ←CHI_BASE_LOOKUP_TABLE.eq_def,
          ←CHI_BASE_LOOKUP_TABLE.eq_def,
          ←CHI_BASE_LOOKUP_TABLE.eq_def,
          ←CHI_BASE_LOOKUP_TABLE.eq_def,
        ]
        have h_bv_a: a = (1755 - 2*x0.val + x1.val - x2.val) % 8 := by
          rewrite [h_input]
          omega
        have h_bv_b: b = ((1755 - 2*x0.val + x1.val - x2.val) % 64) >>> 3 := by
          rewrite [h_input, Nat.shiftRight_eq_div_pow]
          omega
        have h_bv_c: c = ((1755 - 2*x0.val + x1.val - x2.val) % 512) >>> 6 := by
          rewrite [h_input, Nat.shiftRight_eq_div_pow]
          omega
        have h_bv_d: d = (1755 - 2*x0.val + x1.val - x2.val) >>> 9 := by
          rewrite [h_input, Nat.shiftRight_eq_div_pow]
          omega
        rewrite [
          h_x0_norm, h_bv_x0,
          h_x1_norm, h_bv_x1,
          h_x2_norm, h_bv_x2,
          Normalize.normalize_unpacked_toNat_small (by trivial),
          Normalize.normalize_unpacked_toNat_small (by trivial),
          Normalize.normalize_unpacked_toNat_small (by trivial),
          show 2 = (2#192).toNat by decide,
          show 1755 = (1755#192).toNat by decide,
        ] at h_bv_a h_bv_b h_bv_c h_bv_d
        simp only [
          keccak_constants, Normalize.mask_bitvec.eq_def, Nat.reduceMul
        ] at h_bv_a h_bv_b h_bv_c h_bv_d
        have : (2#192).toNat *
          (BitVec.setWidth 192 (BitVec.ofNat 12 x0.val) &&& 896728819340954394833684203315380916586050777780576358985#192 &&&
              BitVec.setWidth 192 (BitVec.allOnes 12)).toNat <
          2 ^ 192
        := by
          simp
          rewrite [
            Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega),
            Nat.and_assoc
          ]
          simp
          have : 2 * (x0.val &&& 585) ≤ 1170 := Nat.mul_le_mul_left 2 Nat.and_le_right
          omega
        have : (1755#192 -
                2#192 *
                  (BitVec.setWidth 192 (BitVec.ofNat 12 x0.val) &&&
                      896728819340954394833684203315380916586050777780576358985#192 &&&
                    BitVec.setWidth 192 (BitVec.allOnes 12))).toNat +
            (BitVec.setWidth 192 (BitVec.ofNat 12 x1.val) &&& 896728819340954394833684203315380916586050777780576358985#192 &&&
                BitVec.setWidth 192 (BitVec.allOnes 12)).toNat <
          2 ^ 192
        := by
          rewrite [BitVec.toNat_sub_of_le (by bv_decide)]
          simp
          have : 2 * (x0.val &&& 585) ≤ 1170 := Nat.mul_le_mul_left 2 Nat.and_le_right
          rewrite [
            Nat.mod_eq_of_lt (a := x0.val) (by omega),
            Nat.mod_eq_of_lt (a := x0.val) (by omega),
            Nat.mod_eq_of_lt (a := x1.val) (by omega),
            Nat.mod_eq_of_lt (a := x1.val) (by omega),
            Nat.mod_eq_of_lt,
            Nat.and_assoc,
            Nat.and_assoc,
          ]
          . simp
            have : x1.val &&& 585 ≤ 585 := Nat.and_le_right
            omega
          . rewrite [Nat.and_assoc]; simp; omega
        rewrite [
          ←BitVec.toNat_mul_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
          ←BitVec.toNat_add_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
        ] at h_bv_a
        rewrite [
          ←BitVec.toNat_mul_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
          ←BitVec.toNat_add_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
        ] at h_bv_b
        rewrite [
          ←BitVec.toNat_mul_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
          ←BitVec.toNat_add_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
        ] at h_bv_c
        rewrite [
          ←BitVec.toNat_mul_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
          ←BitVec.toNat_add_of_lt (by assumption),
          ←BitVec.toNat_sub_of_le (by bv_decide),
        ] at h_bv_d
        rewrite [show 8 = (8#192).toNat by decide] at h_bv_a
        rewrite [show 64 = (64#192).toNat by decide] at h_bv_b
        rewrite [show 512 = (512#192).toNat by decide] at h_bv_c
        rewrite [
          ←BitVec.toNat_umod
        ] at h_bv_a h_bv_b h_bv_c
        rewrite [
          ←BitVec.toNat_ushiftRight
        ] at h_bv_b h_bv_c h_bv_d
        set bv_x0 := BitVec.ofNat 12 x0.val
        set bv_x1 := BitVec.ofNat 12 x1.val
        set bv_x2 := BitVec.ofNat 12 x2.val
        rewrite [
          chi_base_lookup_table_combine_to_bitvec
            h_a (by bv_omega) h_bv_a
            h_b (by bv_omega) h_bv_b
            h_c (by bv_omega) h_bv_c
            h_d (by bv_omega) h_bv_d
        ]
        congr 1
        unfold chi_base_lookup
        bv_decide
      . simp [←CHI_BASE_LOOKUP_TABLE.eq_def]
        set a' := CHI_BASE_LOOKUP_TABLE ⟨a, _⟩; have : a' ≤ 1 := chi_base_lookup_table_range _
        set b' := CHI_BASE_LOOKUP_TABLE ⟨b, _⟩; have : b' ≤ 1 := chi_base_lookup_table_range _
        set c' := CHI_BASE_LOOKUP_TABLE ⟨c, _⟩; have : c' ≤ 1 := chi_base_lookup_table_range _
        set d' := CHI_BASE_LOOKUP_TABLE ⟨d, _⟩; have : d' ≤ 1 := chi_base_lookup_table_range _
        omega

  end ChiBase

end Keccak.Soundness.Lookups

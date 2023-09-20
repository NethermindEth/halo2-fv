import Halo2Fv.Zcash.CondSwap
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.NeZero

lemma prime_NeZero {P} (hP: Nat.Prime P): NeZero P := by
  have h: P ≠ 0 := Nat.Prime.ne_zero hP
  rewrite [←neZero_iff] at h
  exact h

-- lemma eq_val_of_sub_eq_zero {P} (hP: Nat.Prime P) (x y: ZMod P) (hZero: x - y = 0) : x.val = y.val := by
--   rewrite [sub_eq_add_neg] at hZero
--   -- rewrite [←ZMod.val_injective] at hZero
--   have hP_NeZero : NeZero P := prime_NeZero hP
--   have hVal: (x + -y).val = ZMod.val 0 := by rw [hZero]
--   rewrite [ZMod.val_add, ZMod.val_zero] at hVal
--   have hDiv : P ∣ ZMod.val x + ZMod.val (-y) := Nat.dvd_of_mod_eq_zero hVal
--   rewrite [Nat.eq_zero_of_dvd_of_lt]



lemma inv_of_inv {P} (a: ZMod P): a⁻¹ = ZMod.inv P a := by
  rw [Inv.inv, ZMod.instInvZMod]

lemma inv_mul_eq_gcd {P} (a : ZMod P): a⁻¹ * a = Nat.gcd a.val P := by
  rw [←ZMod.mul_inv_eq_gcd, mul_comm]

lemma inv_mul_eq_one_of_prime {P} (hP: Nat.Prime P) (a: ZMod P) (hA: a ≠ 0):  a⁻¹ * a = 1 := by
  rewrite [inv_mul_eq_gcd]
  have hP_NeZero: NeZero P := prime_NeZero hP
  refine Iff.mpr (ZMod.nat_coe_zmod_eq_iff P (Nat.gcd (ZMod.val a) P) 1) ?_
  apply Exists.intro 0
  rewrite [mul_zero, add_zero]
  have h: @ZMod.val P 1 = 1 := by
    have hOne_lt_P : Fact (1 < P) := fact_iff.mpr (Nat.Prime.one_lt hP)
    refine ZMod.val_one P
  rewrite [h]
  rewrite [←Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm]
  apply Nat.coprime_of_lt_prime
  . apply Nat.zero_lt_of_ne_zero
    simp only [ne_eq, ZMod.val_eq_zero, not_false_eq_true, hA]
  . simp [ZMod.val_lt]
  . exact hP

lemma ZMod.no_zero_divisors_of_prime (hP: Nat.Prime P) : NoZeroDivisors (ZMod P) := by
  have h_eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : ZMod P}, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b h_mul_eq_zero
    rewrite [←ZMod.val_eq_zero, ZMod.val_mul] at h_mul_eq_zero
    have h_div : P ∣ (a.val * b.val) := Nat.dvd_of_mod_eq_zero h_mul_eq_zero
    have h : P ∣ a.val ∨ P ∣ b.val := (Nat.Prime.dvd_mul hP).mp h_div
    have h_P_NeZero : NeZero P := prime_NeZero hP
    cases h with
      | inl h_a =>
        have h_a_lt_p : ZMod.val a < P := ZMod.val_lt a
        left
        rewrite [←ZMod.val_eq_zero]
        exact Nat.eq_zero_of_dvd_of_lt h_a h_a_lt_p
      | inr h_b =>
        have h_b_lt_p: ZMod.val b < P := ZMod.val_lt b
        right
        rewrite [←ZMod.val_eq_zero]
        exact Nat.eq_zero_of_dvd_of_lt h_b h_b_lt_p
  -- have h_NoZeroDivisors: NoZeroDivisors (ZMod P) := by
  exact {eq_zero_or_eq_zero_of_mul_eq_zero := h_eq_zero_or_eq_zero_of_mul_eq_zero}

lemma zero_or_one {P} (x: ZMod P) (hP: Nat.Prime P) (hX: x * (1-x) = 0) : (x.val=0 ∨ x.val=1) := by
  rcases P with _ | P
  · aesop
  · simp only [ZMod, ZMod.val] at x ⊢
    rcases x with ⟨_ | _ | x, hx⟩ <;> simp
    injection hX with eq
    simp at eq
    have : x.succ < P := by linarith
    have eq₁ : 1 ≤ P - x := by rw [Nat.succ_eq_add_one] at this; apply Nat.le_sub_of_add_le; linarith
    have eq₂ : x ≤ P := by linarith
    have eq₃ : 1 + (P - (x + 1)) = P - x := by rw [Nat.sub_add_eq]; zify [eq₁, eq₂]; norm_num
    rw [eq₃, Nat.mod_eq_of_lt (a := P - x) (by zify [eq₂]; linarith), ←Nat.dvd_iff_mod_eq_zero, Nat.dvd_mul] at eq
    rcases eq with ⟨y, z, ⟨h₁, h₂, h₃⟩⟩
    rw [←h₃, Nat.prime_mul_iff] at hP
    rcases hP with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
    · subst h₅; simp at *; subst h₃
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hx] at h₁
      cases h₁
    · subst h₅; simp at *; subst h₃
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt] at h₂; rw [h₂] at eq₁
      cases eq₁
      zify [eq₂]
      linarith

lemma mul_val_one {P} (x y: ZMod P) (hP: Nat.Prime P) (hOne: ZMod.val x = 1): ZMod.val (x * y) = ZMod.val y := by
  rewrite [ZMod.val_mul, hOne, one_mul, Nat.mod_eq_of_lt]
  . rfl
  . have hP_ne_zero: NeZero P := prime_NeZero hP
    apply ZMod.val_lt

lemma val_one_sub_val_one {P} (x: ZMod P) (hP: Nat.Prime P) (hOne: ZMod.val x = 1): ZMod.val (1 - x) = 0 := by
  have P_NeZero := prime_NeZero hP
  rewrite [sub_eq_add_neg, ZMod.val_add]
  have one_lt_P: 1 < P := Nat.Prime.one_lt hP
  rewrite [ZMod.neg_val', hOne]
  rewrite [ZMod.val_one_eq_one_mod]
  have hP_sub_one: (P - 1) % P = P - 1 := by
    rw [Nat.mod_eq_of_lt]
    apply Nat.sub_lt
    exact Nat.lt_trans zero_lt_one one_lt_P
    exact zero_lt_one
  rewrite [hP_sub_one]
  rw [Nat.mod_eq_of_lt one_lt_P, Nat.add_sub_cancel' (le_of_lt one_lt_P), Nat.mod_self]
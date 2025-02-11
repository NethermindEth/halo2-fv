import Mathlib.Data.ZMod.Basic
import Examples.Attributes

lemma ge_of_ne_of_gt {a b: ℕ}: b < a → a ≠ b+1 → b+2 ≤ a := by
  intro h_gt h_ne
  have h: b+1 ≤ a := by aesop
  cases h with
    | refl => aesop
    | step h' => aesop

lemma ge_succ_of_not_le {a b: ℕ}: ¬a ≤ b → b+1 ≤ a := by
  intro not_le
  aesop

lemma le_of_le_of_ne {a b: ℕ}: a ≠ b + 1 → a ≤ b + 1 → a ≤ b := by
  intro h_ne h_le
  exact Nat.le_of_lt_succ (lt_of_le_of_ne h_le h_ne)

lemma list_rotateLeft_eq_of_eq_rotateRight {l l': List T} (h: l = l'.rotateRight k): l.rotateLeft k = l' := by
  subst h
  simp [List.rotateLeft, List.rotateRight]
  split
  next h => simp_all only
  next
    h =>
    simp_all only [not_le, List.length_append, List.length_drop, List.length_take, tsub_le_iff_right,
      le_add_iff_nonneg_right, zero_le, min_eq_left, Nat.sub_add_cancel]
    split
    next h_1 => cases l' with
      | nil => simp
      | cons head tail =>
        have h_tail: tail = [] := by
          simp [List.length] at h_1
          assumption
        subst h_tail
        simp [List.length, Nat.mod_one]
    next h_1 =>
      simp_all only [not_le]
      simp [List.drop_append_eq_append_drop, List.take_append_eq_append_take]
      have h1: k % l'.length + (l'.length - k % l'.length) = l'.length := by
        refine Nat.add_sub_of_le ?h
        apply le_of_lt
        apply Nat.mod_lt
        linarith
      simp [h1]
      have h2: (k % l'.length - (l'.length - (l'.length - k % l'.length))) = 0 := by
        generalize h_x: k % l'.length = x
        have h_x_range: x < l'.length := by simp [←h_x]; apply Nat.mod_lt; linarith
        simp [Nat.sub_sub_eq_min, min_eq_right (le_of_lt h_x_range)]
      simp [h2]
      sorry


lemma split_add [Add G] (a b c d: G) (h1: a = c) (h2: b = d): a + b = c + d := by
  rewrite [h1, h2]
  rfl

lemma no_zero_divisors_zmod_p {P: ℕ} (P_Prime: Nat.Prime P): NoZeroDivisors (ZMod P) := by
  have fact_prime : Fact P.Prime := by simp [fact_iff, P_Prime]
  refine IsDomain.to_noZeroDivisors (ZMod P)

lemma zmod_pow {P: ℕ} (a b c:ℕ) (h: a^b=c): ((a: ZMod P)^b) = (c: ZMod P) := by
  aesop

@[zmod_pow_simps] lemma zmod_2pow3 : 2^3 = (8: ZMod P) := by
  have h := @zmod_pow P 2 3 8 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow6 : 2^6 = (64: ZMod P) := by
  have h := @zmod_pow P 2 6 64 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow9 : 2^9 = (512: ZMod P) := by
  have h := @zmod_pow P 2 9 512 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow12 : 2^12 = (4096: ZMod P) := by
  have h := @zmod_pow P 2 12 4096 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow18 : 2^18 = (262144: ZMod P) := by
  have h := @zmod_pow P 2 18 262144 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow21 : 2^21 = (2097152: ZMod P) := by
  have h := @zmod_pow P 2 21 2097152 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow24 : 2^24 = (16777216: ZMod P) := by
  have h := @zmod_pow P 2 24 16777216 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow33 : 2^33 = (8589934592: ZMod P) := by
  have h := @zmod_pow P 2 33 8589934592 (by trivial)
  aesop

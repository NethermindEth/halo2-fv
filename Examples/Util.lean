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

lemma list_rotateLeft_mod{l: List T}: l.rotateLeft (k % l.length) = l.rotateLeft k := by
  unfold List.rotateLeft
  aesop

lemma list_rotateRight_mod{l: List T}: l.rotateRight (k % l.length) = l.rotateRight k := by
  unfold List.rotateRight
  aesop

lemma list_rotateLeft_length{l: List T}: (l.rotateLeft k).length = l.length := by
  simp [List.rotateLeft]
  split
  next h => simp_all only
  next h =>
    simp_all only [not_le, List.length_append, List.length_drop, List.length_take]
    rw [min_eq_left, Nat.sub_add_cancel]
    . apply le_of_lt
      apply Nat.mod_lt
      linarith
    . apply le_of_lt
      apply Nat.mod_lt
      linarith

lemma list_rotateRight_length{l: List T}: (l.rotateRight k).length = l.length := by
  simp [List.rotateRight]
  aesop

lemma list_rotateLeft_eq_of_eq_rotateRight {l l': List T} (h: l = l'.rotateRight k): l.rotateLeft k = l' := by
  subst h
  simp only [List.rotateLeft, list_rotateRight_length]
  simp only [List.rotateRight]
  if h_l': l'.length ≤ 1
  then simp [h_l']
  else {
    simp [h_l']
    simp [List.drop_append_eq_append_drop]
    generalize h_a: k % l'.length = a
    generalize h_b: l'.length - a = b
    have h_a_range: a < l'.length := by rewrite [←h_a]; apply Nat.mod_lt; linarith
    have h_len_sub_b : l'.length - b = a := by rw [←h_b, Nat.sub_sub_eq_min, min_eq_right]; exact le_of_lt h_a_range
    rewrite [h_len_sub_b]
    have h_a_plus_b : a + b = l'.length := by simp [←h_b, Nat.add_sub_cancel' (le_of_lt h_a_range)]
    simp [h_a_plus_b]
    apply List.ext_get?
    intro n
    simp [List.getElem?_append]
    have h_b_range: b ≤ l'.length := by simp [←h_b]
    if h_n_length : n < l'.length
    then {
      simp [h_n_length]
      aesop
    }
    else {
      simp [h_n_length, min_eq_left h_b_range, List.getElem?_take]
      have h_oob: n - b ≥ a := by
        simp only [ge_iff_le]
        rewrite [Nat.le_sub_iff_add_le, h_a_plus_b]
        . exact Nat.le_of_not_gt h_n_length
        . linarith
      rewrite [ite_cond_eq_false]
      simp [*]
      linarith
      aesop
    }
  }

lemma list_eq_rotateRight_of_rotateLeft_eq {l l': List T} (h: l.rotateLeft k = l'): l = l'.rotateRight k := by
  subst h
  simp only [List.rotateRight, list_rotateLeft_length]
  simp only [List.rotateLeft]
  if h_l: l.length ≤ 1
  then simp [h_l]
  else simp [h_l]

lemma split_add [Add G] (a b c d: G) (h1: a = c) (h2: b = d): a + b = c + d := by
  rewrite [h1, h2]
  rfl

lemma no_zero_divisors_zmod_p {P: ℕ} (P_Prime: Nat.Prime P): NoZeroDivisors (ZMod P) := by
  have fact_prime : Fact P.Prime := by simp [fact_iff, P_Prime]
  refine IsDomain.to_noZeroDivisors (ZMod P)

lemma zmod_p_one_neq_zero {P: ℕ} (P_Prime: Nat.Prime P) : (1: ZMod P) ≠ (0: ZMod P) := by
  simp_all only [ne_eq]
  apply Aesop.BuiltinRules.not_intro
  intro a
  have h: (1: ZMod P).val = 0 := by simp [ZMod.val_eq_one, a]
  rw [ZMod.val_one_eq_one_mod] at h
  rw [Nat.one_mod_eq_zero_iff] at h
  rw [h] at P_Prime
  contradiction

lemma zmod_not_zero_eq_one {P: ℕ} {P_Prime: Nat.Prime P}: ((@OfNat.ofNat (ZMod P) 0 Zero.toOfNat0) = (@OfNat.ofNat (ZMod P) 1 One.toOfNat1)) = False := by
  have h := zmod_p_one_neq_zero P_Prime
  aesop

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

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Basic
import Examples.Attributes

lemma nat_shiftLeft_eq_mul_comm:
  n <<< m = 2^m * n
:= by
  simp [Nat.shiftLeft_eq, mul_comm]

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

lemma list_rotateLeft_mod {l: List T}: l.rotateLeft (k % l.length) = l.rotateLeft k := by
  unfold List.rotateLeft
  aesop

lemma list_rotateRight_mod {l: List T}: l.rotateRight (k % l.length) = l.rotateRight k := by
  unfold List.rotateRight
  aesop

lemma list_rotateLeft_length {l: List T}: (l.rotateLeft k).length = l.length := by
  simp [List.rotateLeft]
  split
  next h => simp_all only
  next h =>
    simp_all only [not_le, List.length_append, List.length_drop, List.length_take]
    rw [min_eq_left, Nat.sub_add_cancel] <;> apply le_of_lt <;> apply Nat.mod_lt _ <;> omega

lemma list_rotateRight_length {l: List T}: (l.rotateRight k).length = l.length := by
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
    have h_a_range: a < l'.length := by rewrite [←h_a]; apply Nat.mod_lt; omega
    have h_len_sub_b : l'.length - b = a := by rw [←h_b, Nat.sub_sub_eq_min, min_eq_right]; exact le_of_lt h_a_range
    rewrite [h_len_sub_b]
    have h_a_plus_b : a + b = l'.length := by simp [←h_b, Nat.add_sub_cancel' (le_of_lt h_a_range)]
    simp [h_a_plus_b]
    apply List.ext_getElem?
    intro n
    simp [List.getElem?_append]
    have h_b_range: b ≤ l'.length := by simp [←h_b]
    have h_b_plus_a : b + a = l'.length := by simp [add_comm, h_a_plus_b]
    simp_all [List.getElem?_take]
    split_ifs
    . rfl
    . omega
    . congr
      omega
  }

lemma list_eq_rotateRight_of_rotateLeft_eq {l l': List T} (h: l.rotateLeft k = l'): l = l'.rotateRight k := by
  subst h
  simp only [List.rotateRight, list_rotateLeft_length]
  simp only [List.rotateLeft]
  if h_l: l.length ≤ 1
  then simp [h_l]
  else simp [h_l]

-- def range (n : Nat) : List Nat :=
--   loop n []
-- where
--   loop : Nat → List Nat → List Nat
--   | 0,   acc => acc
--   | n+1, acc => loop n (n::acc)

@[list_ops] lemma list_ops_foldr_nil : List.foldr f init [] = init := rfl
@[list_ops] lemma list_ops_foldr_cons : List.foldr f init (a::l) = f a (List.foldr f init l) := rfl
@[list_ops] lemma list_ops_range_eq_loop: List.range n = List.range.loop n [] := rfl
@[list_ops] lemma list_ops_range_loop_zero: List.range.loop 0 acc = acc := rfl
@[list_ops] lemma list_ops_range_loop_succ: List.range.loop (n+1) acc = List.range.loop n (n::acc) := rfl
@[list_ops] lemma list_ops_rotateRight_nil: List.rotateRight (α := α) [] n = [] := rfl
@[list_ops] lemma list_ops_rotateRight_singleton: List.rotateRight [a] n = [a] := rfl
@[list_ops] lemma list_ops_rotateRight_cons_cons : (a::b::c).rotateRight n = List.drop (c.length+2 - n % (c.length+2)) (a::b::c) ++ List.take (c.length+2 - n % (c.length+2)) (a::b::c) := by simp [List.rotateRight]
-- @[list_ops] lemma list_ops_rotateRight_cons_one: (l::ls).rotateRight = List.drop ls.length (l::ls) ++ List.take ls.length (l::ls) := by
--   simp [List.rotateRight]
--   split_ifs
--   . have : ls.length = 0 := by omega
--     simp_all
--   . rewrite [Nat.mod_eq_of_lt (by omega)]
--     norm_num

-- @[list_ops] lemma list_ops_rotateRight_succ {l: List T} : l.rotateRight n.succ = (l.rotateRight).rotateRight n := by
--   cases l with
--     | nil => simp [list_ops]
--     | cons head tail => cases tail with
--       | nil => simp [list_ops]
--       | cons neck tail =>
--         simp [List.rotateRight, add_comm]
--         have : 1+ (tail.length + 1) = tail.length + 2 := by omega
--         simp [this]
--         by_cases h_rot: (n+1) % (tail.length + 2) = 0
--         . have h_n: n % (tail.length + 2) = tail.length + 1 := by
--             have := Nat.mod_eq_iff.mp h_rot
--             cases this with
--               | inl h => omega
--               | inr h =>
--                 obtain ⟨_, ⟨k, h_k⟩⟩ := h
--                 rewrite [Nat.eq_sub_of_add_eq h_k]
--                 apply Nat.mod_eq_iff.mpr
--                 simp
--                 cases k with
--                   | zero => simp_all
--                   | succ k =>
--                     use k
--                     simp [mul_add]
--           simp_all
--         . have h_n: n % (tail.length + 2) = (n+1) % (tail.length + 2) - 1 := by
--             simp [Nat.mod_eq_iff] at h_rot
--             rewrite [Nat.mod_eq_iff]
--             right
--             split_ands
--             . have := Nat.mod_lt (n+1) (y := tail.length+2) (by omega)
--               omega
--             . use (n+1)/(tail.length + 2)
--               have ⟨h, h'⟩ := (Nat.div_mod_unique (a := n+1) (b := tail.length+2) (d := (n+1)/(tail.length+2)) (c := (n+1) % (tail.length+2)) (by omega)).mp ⟨rfl, rfl⟩
--               have := Nat.sub_eq_of_eq_add h
--               rewrite (occs := .pos [1]) [←this]
--               rewrite [add_comm]
--               apply Nat.add_sub_assoc
--               by_cases h_zero: (n+1) % (tail.length+2) = 0
--               . exfalso
--                 rewrite [Nat.mod_eq_iff] at h_zero
--                 cases h_zero with
--                   | inl => omega
--                   | inr h_zero =>
--                     obtain ⟨_, ⟨k, h_zero⟩⟩ := h_zero
--                     simp_all
--               . omega
--           simp [h_n, List.drop_append_eq_append_drop]





lemma split_add [Add G] (a b c d: G) (h1: a = c) (h2: b = d): a + b = c + d := by
  rewrite [h1, h2]
  rfl

lemma no_zero_divisors_zmod_p {P: ℕ} (P_Prime: Nat.Prime P): NoZeroDivisors (ZMod P) := by
  have fact_prime : Fact P.Prime := by simp [fact_iff, P_Prime]
  exact IsDomain.to_noZeroDivisors (ZMod P)

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

lemma ofNat_zmod_val [NeZero P] (a: ZMod P): a = a.val := by simp

lemma zmod_val_ofNat [Nat.AtLeastTwo n]: ZMod.val (@OfNat.ofNat (ZMod P) n _) = n % P := by
    rewrite [←Nat.cast_ofNat, ZMod.val_natCast]
    rfl

lemma zmod_val_ofNat_of_lt [Nat.AtLeastTwo n] (h: n < P): ZMod.val (@OfNat.ofNat (ZMod P) n _) = n := by
  rewrite [←Nat.cast_ofNat, ZMod.val_natCast_of_lt]
  . rfl
  . exact h

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

@[zmod_pow_simps] lemma zmod_2pow32 : 2^32 = (4294967296: ZMod P) := by
  have h := @zmod_pow P 2 32 4294967296 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow33 : 2^33 = (8589934592: ZMod P) := by
  have h := @zmod_pow P 2 33 8589934592 (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow36 : 2^36 = (68719476736 : ZMod P) := by
  have h := @zmod_pow P 2 36 68719476736  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow48 : 2^48 = (281474976710656 : ZMod P) := by
  have h := @zmod_pow P 2 48 281474976710656  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow54 : 2^54 = (18014398509481984 : ZMod P) := by
  have h := @zmod_pow P 2 54 18014398509481984  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow60 : 2^60 = (1152921504606846976 : ZMod P) := by
  have h := @zmod_pow P 2 60 1152921504606846976  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow72 : 2^72 = (4722366482869645213696 : ZMod P) := by
  have h := @zmod_pow P 2 72 4722366482869645213696  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow84 : 2^84 = (19342813113834066795298816 : ZMod P) := by
  have h := @zmod_pow P 2 84 19342813113834066795298816  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow90 : 2^90 = (1237940039285380274899124224 : ZMod P) := by
  have h := @zmod_pow P 2 90 1237940039285380274899124224  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow96 : 2^96 = (79228162514264337593543950336 : ZMod P) := by
  have h := @zmod_pow P 2 96 79228162514264337593543950336  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow108 : 2^108 = (324518553658426726783156020576256 : ZMod P) := by
  have h := @zmod_pow P 2 108 324518553658426726783156020576256  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow120 : 2^120 = (1329227995784915872903807060280344576 : ZMod P) := by
  have h := @zmod_pow P 2 120 1329227995784915872903807060280344576  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow126 : 2^126 = (85070591730234615865843651857942052864 : ZMod P) := by
  have h := @zmod_pow P 2 126 85070591730234615865843651857942052864  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow132 : 2^132 = (5444517870735015415413993718908291383296 : ZMod P) := by
  have h := @zmod_pow P 2 132 5444517870735015415413993718908291383296  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow144 : 2^144 = (22300745198530623141535718272648361505980416 : ZMod P) := by
  have h := @zmod_pow P 2 144 22300745198530623141535718272648361505980416  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow156 : 2^156 = (91343852333181432387730302044767688728495783936 : ZMod P) := by
  have h := @zmod_pow P 2 156 91343852333181432387730302044767688728495783936  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow162 : 2^162 = (5846006549323611672814739330865132078623730171904 : ZMod P) := by
  have h := @zmod_pow P 2 162 5846006549323611672814739330865132078623730171904  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow168 : 2^168 = (374144419156711147060143317175368453031918731001856 : ZMod P) := by
  have h := @zmod_pow P 2 168 374144419156711147060143317175368453031918731001856  (by trivial)
  aesop

@[zmod_pow_simps] lemma zmod_2pow180 : 2^180 = (1532495540865888858358347027150309183618739122183602176 : ZMod P) := by
  have h := @zmod_pow P 2 180 1532495540865888858358347027150309183618739122183602176  (by trivial)
  aesop

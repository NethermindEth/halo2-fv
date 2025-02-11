import Examples.ScrollKeccak
import Mathlib.Data.ZMod.Basic
import Examples.Util

namespace Scroll.Keccak

def spec (c: ValidCircuit P P_Prime): Prop := sorry

-- gates

section round

  section split
    def offset_sum (column: ℕ → ZMod P) (n offset row: ℕ): ℕ → ZMod P
      | .zero => 0
      | .succ x => (2^(offset*x)) * column ((row + x) % n) + offset_sum column n offset row x
  end split

end round

def round_split (c: ValidCircuit P P_Prime) (a b: ℕ → ZMod P) (row: ℕ) : Prop := (
        (2^165) * a ((row + 5) % c.n) +
        (2^132) * a ((row + 4) % c.n) +
        (2^99) * a ((row + 3) % c.n) +
        (2^66) * a ((row + 2) % c.n) +
        (2^33) * a ((row + 1) % c.n) +
        (2^0) * a ((row + 0) % c.n)
          =
        b ((row + 2) % c.n) +
        b ((row + 1) % c.n)
      )

  -- Gate number 1008 name: "round" part 1/82 split
lemma round_split_of_gate_0 (c: ValidCircuit P P_Prime) (h_gate: gate_0 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      offset_sum (c.get_advice 10) c.n 33 row 6 =
      c.get_advice 9 ((row + 2) % c.n) + c.get_advice 9 ((row + 1) % c.n)
  )) := by
    unfold gate_0 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        replace h_gate := h_gate row
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_zero_or_eq_zero_of_mul_eq_zero h_gate
        replace h_gate := (or_iff_right (hnon_zero.out)).mp h_gate
        replace h_gate := eq_neg_of_add_eq_zero_left h_gate
        rewrite [neg_add, neg_involutive, neg_involutive] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow33]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 2/82 absorb result
lemma round_absorb_result_of_gate_1 (c: ValidCircuit P P_Prime) (h_gate: gate_1 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      offset_sum (c.get_advice 11) c.n 33 row 6 =
      c.get_advice 9 ((row + 3) % c.n)
  )) := by
    unfold gate_1 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        rewrite [neg_involutive] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow33]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 3/82 split
lemma round_split_of_gate_2 (c: ValidCircuit P P_Prime) (h_gate: gate_2 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      offset_sum (c.get_advice 12) c.n 24 row 8 =
      c.get_advice 9 ((row + 2) % c.n)
  )) := by
    unfold gate_2 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        replace h_gate := h_gate row
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_zero_or_eq_zero_of_mul_eq_zero h_gate
        replace h_gate := (or_iff_right (hnon_zero.out)).mp h_gate
        replace h_gate := eq_neg_of_add_eq_zero_left h_gate
        rewrite [neg_involutive] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow24]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 4/82 split
lemma round_split_of_gate_3 (c: ValidCircuit P P_Prime) (h_gate: gate_3 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      offset_sum (c.get_advice 15) c.n 21 row 10 =
      c.get_advice 7 row +
      c.get_advice 7 ((row + 1) % c.n) +
      c.get_advice 7 ((row + 2) % c.n) +
      c.get_advice 7 ((row + 3) % c.n) +
      c.get_advice 7 ((row + 4) % c.n)
  )) := by
    unfold gate_3 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_add_rev, neg_neg] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow21]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 5/82 split
lemma round_split_of_gate_4 (c: ValidCircuit P P_Prime) (h_gate: gate_4 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      (2^42) * offset_sum (c.get_advice 16) c.n 21 row 8 +
      offset_sum (c.get_advice 15) c.n 21 (row+10) 2 =
      c.get_advice 7 ((row + 5) % c.n) +
      c.get_advice 7 ((row + 6) % c.n) +
      c.get_advice 7 ((row + 7) % c.n) +
      c.get_advice 7 ((row + 8) % c.n) +
      c.get_advice 7 ((row + 9) % c.n)
  )) := by
    unfold gate_4 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_add_rev, neg_neg] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow21]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 6/82 split
lemma round_split_of_gate_5 (c: ValidCircuit P P_Prime) (h_gate: gate_5 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      (2^84) * offset_sum (c.get_advice 17) c.n 21 row 6 +
      offset_sum (c.get_advice 16) c.n 21 (row+8) 4 =
      c.get_advice 7 ((row + 10) % c.n) +
      c.get_advice 7 ((row + 11) % c.n) +
      c.get_advice 8 row +
      c.get_advice 8 ((row + 1) % c.n) +
      c.get_advice 8 ((row + 2) % c.n)
  )) := by
    unfold gate_5 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_add_rev, neg_neg] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow21]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 7/82 split
lemma round_split_of_gate_6 (c: ValidCircuit P P_Prime) (h_gate: gate_6 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      (2^(21*6)) * offset_sum (c.get_advice 18) c.n 21 row 4 +
      offset_sum (c.get_advice 17) c.n 21 (row+6) 6 =
      c.get_advice 8 ((row + 3) % c.n) +
      c.get_advice 8 ((row + 4) % c.n) +
      c.get_advice 8 ((row + 5) % c.n) +
      c.get_advice 8 ((row + 6) % c.n) +
      c.get_advice 8 ((row + 7) % c.n)
  )) := by
    unfold gate_6 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_add_rev, neg_neg] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow21]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 8/82 split
lemma round_split_of_gate_7 (c: ValidCircuit P P_Prime) (h_gate: gate_7 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      (2^(21*8)) * offset_sum (c.get_advice 19) c.n 21 row 2 +
      offset_sum (c.get_advice 18) c.n 21 (row+4) 8 =
      c.get_advice 8 ((row + 8) % c.n) +
      c.get_advice 8 ((row + 9) % c.n) +
      c.get_advice 8 ((row + 10) % c.n) +
      c.get_advice 8 ((row + 11) % c.n) +
      c.get_advice 9 row
  )) := by
    unfold gate_7 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_add_rev, neg_neg] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←h_gate]
        simp only [pow_zero, add_zero, h_row_range, Nat.mod_eq_of_lt, one_mul, mul_add, add_left_inj]
        rewrite [←zmod_2pow21]
        simp only [← mul_assoc, ← pow_add, Nat.reduceAdd, add_assoc]

  -- Gate number 1008 name: "round" part 9/82 split uniform
lemma round_split_of_gate_8 (c: ValidCircuit P P_Prime) (h_gate: gate_8 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      offset_sum (c.get_advice 25) c.n 24 row 8  =
      c.get_advice 7 row +
      (2^(21*8)) * offset_sum (c.get_advice 24) c.n 21 row 2 +
      offset_sum (c.get_advice 23) c.n 21 (row + 4) 8 +
      8 * (
        (2^(21*2)) * offset_sum (c.get_advice 21) c.n 21 row 7 +
        offset_sum (c.get_advice 20) c.n 21 (row+10) 2
      ) +
      c.get_advice 21 ((row + 7) % c.n)
  )) := by
    unfold gate_8 at h_gate
    intro row h_row_range
    simp only [mul_zero, zero_add, neg_add_rev] at h_gate
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_add_rev, neg_neg] at h_gate
        simp only [offset_sum]
        simp only [zero_add, mul_one, Nat.reduceAdd, Nat.reduceMul]
        rewrite [←zmod_2pow21, ←zmod_2pow24] at h_gate
        simp only [mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd] at h_gate
        simp only [pow_zero, one_mul, add_zero, Nat.mod_eq_of_lt h_row_range, ←add_assoc]
        rewrite [h_gate]
        simp only [← add_assoc, mul_add, ← mul_assoc, ← pow_add, Nat.reduceAdd]

  -- Gate number 1008 name: "round" part 10/82 rot part
lemma round_rot_part_of_gate_9 (c: ValidCircuit P P_Prime) (h_gate: gate_9 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      offset_sum (c.get_advice 85) c.n 3 row 2 =
      c.get_advice 30 ((row +4) % c.n)
  )) := by
    unfold gate_9 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg] at h_gate
        simp only [offset_sum, Nat.reduceMul, pow_zero, one_mul, add_zero, zmod_2pow3]
        rewrite [←h_gate, add_comm, Nat.mod_eq_of_lt h_row_range]
        rfl

  -- Gate number 1008 name: "round" part 11/82 split uniform
lemma round_split_of_gate_10 (c: ValidCircuit P P_Prime) (h_gate: gate_10 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
      (2^21) * (2^(24*7)) * c.get_advice 85 row +
      (2^21) * offset_sum (c.get_advice 30) c.n 24 (row+5) 7 +
      c.get_advice 85 ((row + 1) % c.n) =
      c.get_advice 7 ((row + 5) % c.n) +
      offset_sum (c.get_advice 20) c.n 21 row 10 +
      8 * (
        (2^(21*4)) * offset_sum (c.get_advice 22) c.n 21 row 5 +
        offset_sum (c.get_advice 21) c.n 21 (row + 8) 4
      ) +
      c.get_advice 22 ((row + 5) % c.n)
  )) := by
    unfold gate_10 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [←zmod_2pow21, ←zmod_2pow24, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, neg_neg, ←add_assoc] at h_gate
        simp only [offset_sum, Nat.reduceMul, Nat.reduceAdd, ←pow_add, mul_add, ←mul_assoc, add_assoc]
        simp only [←add_assoc, mul_zero, zero_add, h_gate, add_left_inj, pow_zero, mul_one, add_zero, Nat.mod_eq_of_lt h_row_range, one_mul]

  -- Gate number 1008 name: "round" part 12/82 rot part
lemma round_rot_part_of_gate_11 (c: ValidCircuit P P_Prime) (h_gate: gate_11 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 85) c.n 18 (row+2) 2 =
    c.get_advice 40 ((row + 3) % c.n)
  )) := by
    unfold gate_11 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg] at h_gate
        simp only [←h_gate, offset_sum, mul_one, add_assoc, Nat.reduceAdd, mul_zero, pow_zero, one_mul, add_zero, zmod_2pow18]
        rewrite [add_comm]
        rfl

  -- Gate number 1008 name: "round" part 13/82 split uniform
lemma round_split_of_gate_12 (c: ValidCircuit P P_Prime) (h_gate: gate_12 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    64 * (
      (2^(24*7)) * c.get_advice 85 ((row + 2) % c.n) +
      (2^(24*4)) * offset_sum (c.get_advice 40) c.n 24 row 3 +
      offset_sum (c.get_advice 35) c.n 24 (row + 8) 4
    ) +
    c.get_advice 85 ((row + 3) % c.n) =
    c.get_advice 7 ((row + 10) % c.n) +
    (2^(21*2)) * offset_sum (c.get_advice 21) c.n 21 row 8 +
    offset_sum (c.get_advice 20) c.n 21 (row+10) 2 +
    8* (
      (2^(21*6)) * offset_sum (c.get_advice 23) c.n 21 row 3 +
      offset_sum (c.get_advice 22) c.n 21 (row+6) 6
    ) +
    c.get_advice 23 ((row+3) % c.n)
  )) := by
    unfold gate_12 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [mul_zero, zero_add, neg_neg, ←zmod_2pow24, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd] at h_gate
        simp only [offset_sum, Nat.reduceMul, add_zero, pow_zero, one_mul, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, ←add_assoc, Nat.mod_eq_of_lt h_row_range]
        rewrite [h_gate]
        simp only [←zmod_2pow21, mul_assoc, ←pow_add, Nat.reduceAdd, ←add_assoc, add_left_inj]



  -- Gate number 1008 name: "round" part 14/82 rot part
lemma round_rot_part_of_gate_13 (c: ValidCircuit P P_Prime) (h_gate: gate_13 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 85) c.n 12 (row+4) 2 =
    c.get_advice 25 ((row+11) % c.n)
  )) := by
    unfold gate_13 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow12] at h_gate
        simp only [←h_gate, offset_sum, mul_one, mul_zero, pow_zero, one_mul, add_zero]
        rewrite [add_comm]
        rfl


  -- Gate number 1008 name: "round" part 15/82 split uniform
lemma round_split_of_gate_14 (c: ValidCircuit P P_Prime) (h_gate: gate_14 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    4096 * (
      (2^(24*7)) * c.get_advice 85 ((row + 4) % c.n) +
      (2^(24*4)) * offset_sum (c.get_advice 25) c.n 24 (row+8) 3 +
      offset_sum (c.get_advice 30) c.n 24 row 4
    ) +
    c.get_advice 85 ((row + 5) % c.n) =
    c.get_advice 8 ((row + 3) % c.n) +
    (2^(21*4)) * offset_sum (c.get_advice 22) c.n 21 row 6 +
    offset_sum (c.get_advice 21) c.n 21 (row+8) 4 +
    8 * (
      (2^(21*8)) * c.get_advice 24 row +
      offset_sum (c.get_advice 23) c.n 21 (row+4) 8
    ) +
    c.get_advice 24 ((row+1) % c.n)
  )) := by
    unfold gate_14 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow24, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd] at h_gate
        simp only [offset_sum, Nat.reduceMul, mul_add, ←mul_assoc, ←add_assoc, pow_zero, mul_one, mul_zero, add_zero, ←pow_add, Nat.reduceAdd]
        simp only [add_assoc, Nat.reduceAdd]
        simp only [←add_assoc, Nat.mod_eq_of_lt h_row_range]
        rewrite [h_gate]
        simp only [←zmod_2pow21, mul_assoc, ←pow_add, Nat.reduceAdd]
        simp only [←add_assoc, add_left_inj, one_mul]

  -- Gate number 1008 name: "round" part 16/82 rot part
lemma round_rot_part_of_gate_15 (c: ValidCircuit P P_Prime) (h_gate: gate_15 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 85) c.n 9 (row+6) 2 =
    c.get_advice 35 ((row + 3) % c.n)
  )) := by
    unfold gate_15 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow9] at h_gate
        simp only [←h_gate, offset_sum, add_assoc, Nat.reduceAdd, mul_zero, add_zero, mul_one, pow_zero, one_mul]
        rewrite [add_comm]
        rfl

  -- Gate number 1008 name: "round" part 17/82 split uniform
lemma round_split_of_gate_16 (c: ValidCircuit P P_Prime) (h_gate: gate_16 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    32768 * (
      (2^(24*7)) * c.get_advice 85 ((row + 6) % c.n) +
      (2^(24*4)) * offset_sum (c.get_advice 35) c.n 24 row 3 +
      offset_sum (c.get_advice 35) c.n 24 (row+4) 4
    ) +
    c.get_advice 85 ((row + 7) % c.n) =
    c.get_advice 8 ((row + 8) % c.n) +
    (2^(21*6)) * offset_sum (c.get_advice 23) c.n 21 row 4 +
    offset_sum (c.get_advice 22) c.n 21 (row+6) 6 +
    8 * offset_sum (c.get_advice 20) c.n 21 row 9 +
    c.get_advice 20 ((row + 9) % c.n)
  )) := by
    unfold gate_16 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow21, ←zmod_2pow24, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, mul_zero, zero_add] at h_gate
        simp only [offset_sum, Nat.reduceMul, mul_add, ←mul_assoc, pow_zero, one_mul, mul_zero, add_zero, ←add_assoc, ←pow_add]
        simp only [add_assoc, Nat.reduceAdd]
        simp only [←add_assoc, Nat.mod_eq_of_lt h_row_range]
        rewrite [h_gate]
        simp only [add_assoc, add_right_inj]

  -- Gate number 1008 name: "round" part 18/82 rot part
lemma round_rot_part_of_gate_17 (c: ValidCircuit P P_Prime) (h_gate: gate_17 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 85) c.n 12 (row+8) 2 =
    c.get_advice 36 ((row + 4) % c.n)
  )) := by
    unfold gate_17 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg] at h_gate
        simp only [←h_gate, offset_sum, mul_one, add_zero, add_assoc, Nat.reduceAdd, mul_zero, pow_zero, one_mul, ←zmod_2pow12]
        simp only [add_comm]

  -- Gate number 1008 name: "round" part 19/82 split uniform
lemma round_split_of_gate_18 (c: ValidCircuit P P_Prime) (h_gate: gate_18 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    4096 * (
      (2^(24*7)) * c.get_advice 85 ((row + 8) % c.n) +
      (2^(24*3)) * offset_sum (c.get_advice 36) c.n 24 row 4 +
      offset_sum (c.get_advice 36) c.n 24 (row+5) 3
    ) +
    c.get_advice 85 ((row + 9) % c.n) =
    c.get_advice 7 ((row + 1) % c.n) +
    (2^(21*8)) * offset_sum (c.get_advice 24) c.n 21 row 2 +
    offset_sum (c.get_advice 23) c.n 21 (row+4) 8 +
    8 * (
      (2^(21*2)) * offset_sum (c.get_advice 21) c.n 21 row 7 +
      offset_sum (c.get_advice 20) c.n 21 (row+10) 2
    ) +
    c.get_advice 21 ((row + 7) % c.n)
  )) := by
    unfold gate_18 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow24, ←zmod_2pow21, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd] at h_gate
        simp only [Nat.reduceMul, offset_sum, pow_zero, one_mul, add_zero, Nat.mod_eq_of_lt h_row_range, add_assoc, Nat.reduceAdd, mul_add, ←mul_assoc, ←pow_add]
        simp only [←add_assoc]
        rewrite [h_gate]
        simp only [add_assoc]


  -- Gate number 1008 name: "round" part 20/82 rot part
lemma round_rot_part_of_gate_19 (c: ValidCircuit P P_Prime) (h_gate: gate_19 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 85) c.n 12 (row+10) 2 =
    c.get_advice 26 ((row + 5) % c.n)
  )) := by
    unfold gate_19 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow12] at h_gate
        simp only [←h_gate, offset_sum, mul_one, add_zero, add_assoc, Nat.reduceAdd, mul_zero, pow_zero, one_mul]
        simp only [add_comm]

  -- Gate number 1008 name: "round" part 21/82 split uniform
lemma round_split_of_gate_20 (c: ValidCircuit P P_Prime) (h_gate: gate_20 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    4096 * (
      (2^(24*7)) * c.get_advice 85 ((row + 10) % c.n) +
      (2^(24*2)) * offset_sum (c.get_advice 26) c.n 24 row 5 +
      offset_sum (c.get_advice 26) c.n 24 (row+6) 2
    ) + c.get_advice 85 ((row + 11) % c.n) =
    c.get_advice 7 ((row + 6) % c.n) +
    offset_sum (c.get_advice 20) c.n 21 row 10 +
    8 * (
      (2^(21*4)) * offset_sum (c.get_advice 22) c.n 21 row 5 +
      offset_sum (c.get_advice 21) c.n 21 (row+8) 4
    ) +
    c.get_advice 22 ((row + 5) % c.n)
  )) := by
    unfold gate_20 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [←zmod_2pow24, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, neg_neg, ←zmod_2pow21, add_assoc] at h_gate
        simp only [offset_sum, Nat.reduceMul, add_assoc, Nat.reduceAdd, pow_zero, one_mul, add_zero, mul_add, ←mul_assoc, ←pow_add, Nat.mod_eq_of_lt h_row_range, h_gate]

  -- Gate number 1008 name: "round" part 22/82 rot part
lemma round_rot_part_of_gate_21 (c: ValidCircuit P P_Prime) (h_gate: gate_21 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 86) c.n 18 row 2 =
    c.get_advice 31 ((row + 4) % c.n)
  )) := by
    unfold gate_21 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow18] at h_gate
        simp only [offset_sum, mul_one, mul_zero, pow_zero, one_mul, add_zero, add_comm, zero_add, Nat.mod_eq_of_lt h_row_range, h_gate]

  -- Gate number 1008 name: "round" part 23/82 split uniform
lemma round_split_of_gate_22 (c: ValidCircuit P P_Prime) (h_gate: gate_22 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    64 * (
      (2^(24*7)) * c.get_advice 86 row +
      offset_sum (c.get_advice 31) c.n 24 (row+5) 7
    ) +
    c.get_advice 86 ((row + 1) % c.n) =
    c.get_advice 7 ((row + 11) % c.n) +
    (2^(21*2)) * offset_sum (c.get_advice 21) c.n 21 row 8 +
    offset_sum (c.get_advice 20) c.n 21 (row+10) 2 +
    8 * (
      (2^(21*6)) * offset_sum (c.get_advice 23) c.n 21 row 3 +
      offset_sum (c.get_advice 22) c.n 21 (row+6) 6
    ) +
    c.get_advice 23 ((row + 3) % c.n)
  )) := by
    unfold gate_22 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [←zmod_2pow24, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, neg_neg, ←zmod_2pow21, add_assoc] at h_gate
        simp only [Nat.reduceMul, offset_sum, add_assoc, Nat.reduceAdd, pow_zero, one_mul, add_zero, mul_add, ←mul_assoc, h_gate, add_right_inj, ←pow_add, Nat.mod_eq_of_lt h_row_range]

  -- Gate number 1008 name: "round" part 24/82 rot part
lemma round_rot_part_of_gate_23 (c: ValidCircuit P P_Prime) (h_gate: gate_23 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 86) c.n 21 (row+2) 2 =
    c.get_advice 41 ((row + 2) % c.n)
  )) := by
    unfold gate_23 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [neg_neg, ←zmod_2pow21] at h_gate
        simp only [offset_sum, mul_one, add_assoc, Nat.reduceAdd, mul_zero, pow_zero, one_mul, add_zero, ←h_gate, zero_add]
        rewrite [add_comm]
        rfl

  -- Gate number 1008 name: "round" part 25/82 split uniform
lemma round_split_of_gate_24 (c: ValidCircuit P P_Prime) (h_gate: gate_24 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    8 * (
      (2^(24*7)) * c.get_advice 86 ((row + 2) % c.n) +
      (2^(24*5)) * offset_sum (c.get_advice 41) c.n 24 row 2 +
      (2^(24*1)) * offset_sum (c.get_advice 36) c.n 24 (row+8) 4 +
      c.get_advice 41 ((row + 3) % c.n)
    ) +
    c.get_advice 86 ((row + 3) % c.n) =
    c.get_advice 8 ((row + 4) % c.n) +
    (2^(21*4)) * offset_sum (c.get_advice 22) c.n 21 row 6 +
    offset_sum (c.get_advice 21) c.n 21 (row+8) 4 +
    8 * (
      (2^(21*8)) * c.get_advice 24 row +
      offset_sum (c.get_advice 23) c.n 21 (row+4) 8
    ) +
    c.get_advice 24 ((row + 1) % c.n)
  )) := by
    unfold gate_24 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [←zmod_2pow24, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, add_assoc, neg_neg, ←zmod_2pow21] at h_gate
        simp only [offset_sum, mul_zero, add_zero, Nat.reduceMul, pow_zero, one_mul, add_assoc, Nat.reduceAdd, mul_add, ←mul_assoc, ←pow_add, h_gate, Nat.mod_eq_of_lt h_row_range]

  -- Gate number 1008 name: "round" part 26/82 rot part
lemma round_rot_part_of_gate_25 (c: ValidCircuit P P_Prime) (h_gate: gate_25 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 86) c.n 12 (row+4) 2 =
    c.get_advice 26 ((row + 10) % c.n)
  )) := by
    unfold gate_25 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
      right
      have no_zero_div := no_zero_divisors_zmod_p P_Prime
      replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
      simp only [neg_neg, ←zmod_2pow12] at h_gate
      simp only [offset_sum, mul_one, mul_zero, add_assoc, Nat.reduceAdd, add_zero, pow_zero, one_mul, ←h_gate]
      simp only [add_comm]

  -- Gate number 1008 name: "round" part 27/82 split uniform
lemma round_split_of_gate_26 (c: ValidCircuit P P_Prime) (h_gate: gate_26 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    4096 * (
      (2^(24*7)) * c.get_advice 86 ((row + 4) % c.n) +
      (2^(24*5)) * offset_sum (c.get_advice 26) c.n 24 (row+8) 2 +
      (2^(24*1)) * offset_sum (c.get_advice 31) c.n 24 row 4 +
      c.get_advice 26 ((row + 11) % c.n)
    ) +
    c.get_advice 86 ((row+5) % c.n) =
    c.get_advice 8 ((row + 9) % c.n) +
    (2^(21*6)) * offset_sum (c.get_advice 23) c.n 21 row 4 +
    offset_sum (c.get_advice 22) c.n 21 (row+6) 6 +
    8*(
      offset_sum (c.get_advice 20) c.n 21 row 9
    ) +
    c.get_advice 20 ((row + 9) % c.n)
  )) := by
    unfold gate_26 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
      right
      have no_zero_div := no_zero_divisors_zmod_p P_Prime
      replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
      simp only [←zmod_2pow24, mul_zero, zero_add, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, neg_neg, ←zmod_2pow21, add_assoc] at h_gate
      simp only [offset_sum, add_assoc, mul_add, ←mul_assoc, Nat.reduceMul, Nat.reduceAdd, mul_zero, zero_add, pow_zero, one_mul, h_gate, add_zero, Nat.mod_eq_of_lt h_row_range, ←pow_add]

  -- Gate number 1008 name: "round" part 28/82 rot part
lemma round_rot_part_of_gate_27 (c: ValidCircuit P P_Prime) (h_gate: gate_27 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 86) c.n 9 (row+6) 2 =
    c.get_advice 27 ((row + 8) % c.n)
  )) := by
    unfold gate_27 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
      right
      have no_zero_div := no_zero_divisors_zmod_p P_Prime
      replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
      simp only [neg_neg, ←zmod_2pow9] at h_gate
      simp only [offset_sum, mul_one, add_assoc, Nat.reduceAdd, mul_zero, pow_zero, one_mul, add_zero, ←h_gate]
      simp only [add_comm]

  -- Gate number 1008 name: "round" part 29/82 split uniform
lemma round_split_of_gate_28 (c: ValidCircuit P P_Prime) (h_gate: gate_28 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    32768 * (
      (2^(24*7)) * c.get_advice 86 ((row + 6) % c.n) +
      (2^(24*3)) * offset_sum (c.get_advice 32) c.n 24 row 4 +
      offset_sum (c.get_advice 27) c.n 24 (row+9) 3
    ) +
    c.get_advice 86 ((row + 7) % c.n) =
    c.get_advice 7 ((row + 2) % c.n) +
    (2^(21*8)) * offset_sum (c.get_advice 24) c.n 21 row 2 +
    offset_sum (c.get_advice 23) c.n 21 (row+4) 8 +
    8 * (
      (2^(21*2)) * offset_sum (c.get_advice 21) c.n 21 row 7 +
      offset_sum (c.get_advice 20) c.n 21 (row+10) 2
    ) +
    c.get_advice 21 ((row + 7) % c.n)
  )) := by
    unfold gate_28 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
      right
      have no_zero_div := no_zero_divisors_zmod_p P_Prime
      replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
      simp only [←zmod_2pow24, ←zmod_2pow21, neg_neg, add_assoc, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, mul_zero, zero_add] at h_gate
      simp only [offset_sum, add_assoc, mul_add, ←mul_assoc, ←pow_add, Nat.reduceAdd, Nat.reduceMul, add_zero, Nat.mod_eq_of_lt h_row_range, pow_zero, one_mul, h_gate]

  -- Gate number 1008 name: "round" part 30/82 rot part
lemma round_rot_part_of_gate_29 (c: ValidCircuit P P_Prime) (h_gate: gate_29 c):
  (∀ row: ℕ, (
    c.get_fixed 2 row = 0 ∨
    offset_sum (c.get_advice 86) c.n 6 (row+8) 2 =
    c.get_advice 37 ((row + 1) % c.n)
  )) := by
    unfold gate_29 at h_gate
    intro row
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
      right
      have no_zero_div := no_zero_divisors_zmod_p P_Prime
      replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
      simp only [neg_neg, ←zmod_2pow6] at h_gate
      simp only [offset_sum, add_assoc, Nat.reduceAdd, Nat.reduceMul, pow_zero, one_mul, add_zero, ←h_gate]
      simp only [add_comm]

  -- Gate number 1008 name: "round" part 31/82 split
lemma round_split_of_gate_30 (c: ValidCircuit P P_Prime) (h_gate: gate_30 c):
  (∀ row: ℕ, row < c.n → (
    c.get_fixed 2 row = 0 ∨
    sorry
  )) := by
    unfold gate_30 at h_gate
    intro row h_row_range
    cases eq_zero_or_neZero (c.get_fixed 2 row) with
      | inl hzero => left; assumption
      | inr hnon_zero =>
        right
        have no_zero_div := no_zero_divisors_zmod_p P_Prime
        replace h_gate := eq_neg_of_add_eq_zero_left ((or_iff_right (hnon_zero.out)).mp (eq_zero_or_eq_zero_of_mul_eq_zero (h_gate row)))
        simp only [←zmod_2pow21, ←zmod_2pow24] at h_gate
        simp only [add_assoc, ←mul_assoc, Nat.reduceAdd, Nat.reduceMul, ←pow_add, mul_add, mul_zero, zero_add, neg_neg] at h_gate
        have h_mul_assoc : ∀ a b c, a * (2: ZMod P)^b * c = a * (2^b * c) := by
          intro a b c
          simp only [mul_assoc]
        simp only [h_mul_assoc] at h_gate
        simp only [←add_assoc, ←mul_add] at h_gate
        simp only [add_assoc] at h_gate
        have h_start : ∀ col k rot,
          2^k * c.get_advice col ((row + (rot+1)) % c.n) + c.get_advice col ((row + rot) % c.n) =
          offset_sum (c.get_advice col) c.n k (row + rot) 2 := by
            intro col k rot
            simp only [offset_sum, mul_one, add_assoc, mul_zero, pow_zero, add_zero, one_mul]
        have h_start' : ∀ col k,
          2^k * c.get_advice col ((row + 1) % c.n) + c.get_advice col row =
          offset_sum (c.get_advice col) c.n k row 2 := by
            intro col k
            simp only [offset_sum, mul_one, add_assoc, mul_zero, pow_zero, add_zero, one_mul, Nat.mod_eq_of_lt h_row_range]
        have h_start'' : ∀ col k x,
          2^k * c.get_advice col ((row + 1) % c.n) + (c.get_advice col row + x) =
          offset_sum (c.get_advice col) c.n k row 2 + x := by
            intro col k x
            simp only [offset_sum, mul_one, add_assoc, mul_zero, pow_zero, add_zero, one_mul, Nat.mod_eq_of_lt h_row_range]
        simp only [h_start, h_start', h_start''] at h_gate
        have h_cont: ∀ col k n m rot rot', (n*k=m) → (rot+n=rot') →
          2^m * c.get_advice col ((row + rot') % c.n) + offset_sum (c.get_advice col) c.n k (row + rot) n =
          offset_sum (c.get_advice col) c.n k (row + rot) (n+1) := by
            intro col k n rot
            simp only [mul_comm, offset_sum, add_assoc]
        simp only [h_cont, Nat.reduceAdd] at h_gate



lemma round (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  intro ⟨
    _, _, _, _, _, _,
    ⟨⟨
      ⟨hround0, hround1, hround2, hround3, hround4, hround5, hround6, hround7, hround8, hround9⟩,
      ⟨hround10, hround11, hround12, hround13, hround14, hround15, hround16, hround17, hround18, hround19⟩,
      ⟨hround20, hround21, hround22, hround23, hround24, hround25, hround26, hround27, hround28, hround29⟩,
      ⟨hround30, hround31, hround32, hround33, hround34, hround35, hround36, hround37, hround38, hround39⟩,
      ⟨hround40, hround41, hround42, hround43, hround44, hround45, hround46, hround47, hround48, hround49⟩,
      ⟨hround50, hround51, hround52, hround53, hround54, hround55, hround56, hround57, hround58, hround59⟩,
      ⟨hround60, hround61, hround62, hround63, hround64, hround65, hround66, hround67, hround68, hround69⟩,
      ⟨hround70, hround71, hround72, hround73, hround74, hround75, hround76, hround77, hround78, hround79⟩,
      ⟨hround80, hround81, hround82, hround83, hround84, hround85, hround86, hround87, hround88, hround89⟩,
      _, _, _, _, _, _, _, _, _, _⟩, _⟩,
    _, _, _, _
  ⟩
  unfold gate_0 at hround0
  replace hround0 := round_split_of_gate c hround0
  unfold gate_2 at hround2
  replace hround2 := round_split_of_gate c hround2
  unfold gate_3 at hround3
  replace hround3 := round_split_of_gate c hround3
  unfold gate_4 at hround4
  replace hround4 := round_split_of_gate c hround4
  unfold gate_5 at hround5
  replace hround5 := round_split_of_gate c hround5
  unfold gate_6 at hround6
  replace hround6 := round_split_of_gate c hround6
  unfold gate_7 at hround7
  replace hround7 := round_split_of_gate c hround7
  unfold gate_8 at hround8
  replace hround8 := round_split_of_gate c hround8
  rw [←two_pow_thirty] at hround0
  sorry

lemma absorb_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma squeeze_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma input_checks_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma first_row_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma is_final_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma padding_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma length_and_data_rlc_gate (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

-- lookups

lemma absorb_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma input_unpack_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma theta_c_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma rho_by_pi_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma pi_part_range_check_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma chi_base_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma iota_lookup (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

lemma squeeze_unpack (c: ValidCircuit P P_Prime): meets_constraints c → sorry := by
  sorry

theorem spec_of_meets_constraints (c: ValidCircuit P P_Prime): meets_constraints c → spec c := by
  sorry

end Scroll.Keccak

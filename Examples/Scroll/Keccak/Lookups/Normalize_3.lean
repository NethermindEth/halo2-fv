import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Lookups.Normalize_3
  -- columns 8 and 9
  -- range = 3
  -- log_height = KECCAK_DEGREE
  def part_size := get_num_bits_per_lookup 3

  lemma part_size_val: part_size = 6 := by
    rewrite [part_size, get_num_bits_per_lookup]
    rewrite [Nat.log_eq_iff] <;> decide

  def input (P: ℕ) (x0 x1 x2 x3 x4 x5: ℕ): ZMod P :=
    ↑(([x0, x1, x2, x3, x4, x5].foldl (
      λ (⟨input, factor⟩: ℕ × ℕ) (input_part: ℕ) =>
        (input + input_part*factor, factor * BIT_SIZE)
    ) (0, 1): ℕ × ℕ).1)

  def output (P: ℕ) (x0 x1 x2 x3 x4 x5: ℕ): ZMod P :=
    ↑(([x0, x1, x2, x3, x4, x5].foldl (
      λ (⟨output, factor⟩: ℕ × ℕ) (input_part: ℕ) =>
        (output + (input_part % 2)*factor, factor * BIT_SIZE)
    ) (0, 1): ℕ × ℕ).1)

  def input_by_row (P: ℕ) (row: ℕ) : ZMod P :=
    input P (row / 243) ((row / 81) % 3) ((row / 27) % 3) ((row / 9) % 3) ((row / 3) % 3) (row % 3)

  lemma input_eval: input P x0 x1 x2 x3 x4 x5 = x0 + x1*BIT_SIZE + x2*BIT_SIZE^2 + x3*BIT_SIZE^3 + x4*BIT_SIZE^4 + x5*BIT_SIZE^5
    := by
      simp [input, ←pow_two, ←Nat.pow_add_one]

  def output_by_row (P: ℕ) (row: ℕ) : ZMod P :=
    output P (row / 243) ((row / 81) % 3) ((row / 27) % 3) ((row / 9) % 3) ((row / 3) % 3) (row % 3)

  def output_0_to_9 (c: ValidCircuit P P_Prime) : ℕ → ZMod P :=
    λ row =>
    if row = 0 then output P 0 0 0 0 0 0  -- 0: normalize_3 output
    else if row = 1 then output P 0 0 0 0 0 1  -- 1: normalize_3 output
    else if row = 2 then output P 0 0 0 0 0 2  -- 2: normalize_3 output
    else if row = 3 then output P 0 0 0 0 1 0  -- 3: normalize_3 output
    else if row = 4 then output P 0 0 0 0 1 1  -- 4: normalize_3 output
    else if row = 5 then output P 0 0 0 0 1 2  -- 5: normalize_3 output
    else if row = 6 then output P 0 0 0 0 2 0  -- 6: normalize_3 output
    else if row = 7 then output P 0 0 0 0 2 1  -- 7: normalize_3 output
    else if row = 8 then output P 0 0 0 0 2 2  -- 8: normalize_3 output
    else if row = 9 then output P 0 0 0 1 0 0  -- 9: normalize_3 output
    else c.1.FixedUnassigned 9 row

  lemma fixed_8_input_0_to_9 (c: ValidCircuit P P_Prime): row ≤ 9 → fixed_func_col_8_0_to_9 c row = input_by_row P row := by
    intro hrow
    match row with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => simp [fixed_func_col_8_0_to_9, input_by_row, input, keccak_constants]
      | x+10 => contradiction

  lemma aux (hrow: row ≤ x+10) (hrow_lower: x+1 ≤ row)
    (h1: row ≠ x+1) (h2: row ≠ x+2)
    (h3: row ≠ x+3) (h4: row ≠ x+4)
    (h5: row ≠ x+5) (h6: row ≠ x+6)
    (h7: row ≠ x+7) (h8: row ≠ x+8)
    (h9: row ≠ x+9) (h10: row ≠ x+10): False
    := by
      have h := le_of_le_of_ne h10 hrow
      have h := le_of_le_of_ne h9 h
      have h := le_of_le_of_ne h8 h
      have h := le_of_le_of_ne h7 h
      have h := le_of_le_of_ne h6 h
      have h := le_of_le_of_ne h5 h
      have h := le_of_le_of_ne h4 h
      have h := le_of_le_of_ne h3 h
      have h := le_of_le_of_ne h2 h
      have h := le_of_le_of_ne h1 h
      linarith

  lemma fixed_8_input_10_to_19 (c: ValidCircuit P P_Prime): 10 ≤ row → row ≤ 19 → fixed_func_col_8_10_to_19 c row = input_by_row P row := by
    intro hrow_lower hrow
    unfold fixed_func_col_8_10_to_19 input_by_row
    if h10: row = 10 then subst h10; rewrite [ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp
    else if h11: row = 11 then subst h11; rewrite [ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp
    else if h12: row = 12 then subst h12; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp
    else if h13: row = 13 then subst h13; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp;
    else if h14: row = 14 then subst h14; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp;
    else if h15: row = 15 then subst h15; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp;
    else if h16: row = 16 then subst h16; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp;
    else if h17: row = 17 then subst h17; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp; simp;
    else if h18: row = 18 then subst h18; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp; simp; simp
    else if h19: row = 19 then subst h19; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp; simp; simp; simp
    else {
      exfalso
      exact aux hrow hrow_lower h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
    }

  lemma fixed_8_input_20_to_29 (c: ValidCircuit P P_Prime): 20 ≤ row → row ≤ 29 → fixed_func_col_8_20_to_29 c row = input_by_row P row := by
    intro hrow_lower hrow
    unfold fixed_func_col_8_20_to_29 input_by_row
    if h20: row = 20 then subst h20; rewrite [ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp
    else if h21: row = 21 then subst h21; rewrite [ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp
    else if h22: row = 22 then subst h22; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp
    else if h23: row = 23 then subst h23; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp;
    else if h24: row = 24 then subst h24; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp;
    else if h25: row = 25 then subst h25; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp;
    else if h26: row = 26 then subst h26; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp;
    else if h27: row = 27 then subst h27; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp; simp;
    else if h28: row = 28 then subst h28; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp; simp; simp
    else if h29: row = 29 then subst h29; rewrite [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true, input_eval]; simp only [keccak_constants]; norm_num; simp; simp; simp; simp; simp; simp; simp; simp; simp; simp
    else {
      exfalso
      exact aux hrow hrow_lower h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
    }

  lemma fixed_9_output_0_to_9 (c: ValidCircuit P P_Prime): fixed_func_col_9_0_to_9 c row = output_0_to_9 c row := by
    simp [fixed_func_col_9_0_to_9, output_0_to_9, output, keccak_constants]

  lemma lookup_0_normalize_3_input (c: ValidCircuit P P_Prime) (hlookup: lookup_0 c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3 x4 x5: ℕ,
      x0 < 3 ∧
      x1 < 3 ∧
      x2 < 3 ∧
      x3 < 3 ∧
      x4 < 3 ∧
      x5 < 3 ∧
      c.get_advice 10 row = input P x0 x1 x2 x3 x4 x5 ∧
      c.get_advice 11 row = output P x0 x1 x2 x3 x4 x5
    := by
      unfold lookup_0 at hlookup
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      have h_input: c.get_fixed 8 lookup_row = input_by_row P lookup_row := by sorry
      have h_output: c.get_fixed 9 lookup_row = output_by_row P lookup_row := by sorry
      rewrite [h_input, h_output, input_by_row, output_by_row] at hlookup
      use lookup_row/243
      use lookup_row/81 % 3
      use lookup_row/27 % 3
      use lookup_row/9 % 3
      use lookup_row/3 % 3
      use lookup_row % 3
      simp_all [Nat.mod_lt]
      sorry

end Keccak.Lookups.Normalize_3

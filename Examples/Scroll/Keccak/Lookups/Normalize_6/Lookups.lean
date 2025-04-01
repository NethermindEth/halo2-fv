import Examples.Scroll.Keccak.Lookups.Normalize_6.Input
import Examples.Scroll.Keccak.Lookups.Normalize_6.Output

namespace Keccak.Lookups.Normalize_6

  def transform_table (P: ℕ) (row: ℕ) :=
    if row < 216 then
      (input_by_row P row, output_by_row P row)
    else
      (input_by_row P 0, output_by_row P 0)

  lemma apply_transform_table (h: transform_table P row = (x,y)) :
    x = input_by_row P (if row < 216 then row else 0) ∧
    y = output_by_row P (if row < 216 then row else 0)
  := by
    unfold transform_table at h
    by_cases row < 216 <;> simp_all
    rewrite [if_neg (by omega)]
    simp_all

  lemma lookup_normalize_6 (col1 col2: ℕ)
    (c: ValidCircuit P P_Prime) (hlookup: ∀ row < c.usable_rows,
      ∃ lookup_row < c.usable_rows,
      (c.get_advice col1 row, c.get_advice col2 row) =
      (c.get_fixed 12 lookup_row, c.get_fixed 13 lookup_row)
    ) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice col1 row = input P x0 x1 x2 ∧
      c.get_advice col2 row = output P x0 x1 x2
    := by
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_12_eq_input_of_lt_usable_rows, fixed_func_col_13_eq_output_of_lt_usable_rows, input_by_row, output_by_row]
      use ((if lookup_row < 216 then lookup_row else 0) / 36)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 216 then lookup_row else 0) / 6 % 6)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 216 then lookup_row else 0) % 6)
      apply And.intro
      . split <;> omega
      apply And.intro
      . rfl
      . rfl

  lemma lookup_2_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_2 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 15 row = input P x0 x1 x2 ∧
      c.get_advice 25 row = output P x0 x1 x2
    := lookup_normalize_6 15 25 c hlookup h_fixed

  lemma lookup_3_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_3 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 16 row = input P x0 x1 x2 ∧
      c.get_advice 26 row = output P x0 x1 x2
    := lookup_normalize_6 16 26 c hlookup h_fixed

  lemma lookup_4_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_4 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 17 row = input P x0 x1 x2 ∧
      c.get_advice 27 row = output P x0 x1 x2
    := lookup_normalize_6 17 27 c hlookup h_fixed

  lemma lookup_5_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_5 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 18 row = input P x0 x1 x2 ∧
      c.get_advice 28 row = output P x0 x1 x2
    := lookup_normalize_6 18 28 c hlookup h_fixed

  lemma lookup_6_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_6 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 19 row = input P x0 x1 x2 ∧
      c.get_advice 29 row = output P x0 x1 x2
    := lookup_normalize_6 19 29 c hlookup h_fixed

  lemma lookup_7_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_7 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 20 row = input P x0 x1 x2 ∧
      c.get_advice 30 row = output P x0 x1 x2
    := lookup_normalize_6 20 30 c hlookup h_fixed

  lemma lookup_8_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_8 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 21 row = input P x0 x1 x2 ∧
      c.get_advice 31 row = output P x0 x1 x2
    := lookup_normalize_6 21 31 c hlookup h_fixed

  lemma lookup_9_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_9 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 22 row = input P x0 x1 x2 ∧
      c.get_advice 32 row = output P x0 x1 x2
    := lookup_normalize_6 22 32 c hlookup h_fixed

  lemma lookup_10_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_10 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 23 row = input P x0 x1 x2 ∧
      c.get_advice 33 row = output P x0 x1 x2
    := lookup_normalize_6 23 33 c hlookup h_fixed

  lemma lookup_11_normalize_6 (c: ValidCircuit P P_Prime) (hlookup: lookup_11 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice 24 row = input P x0 x1 x2 ∧
      c.get_advice 34 row = output P x0 x1 x2
    := lookup_normalize_6 24 34 c hlookup h_fixed

  lemma lookup_2_to_11_normalize_6 (c: ValidCircuit P P_Prime)
    (h_lookup_2: lookup_2 c) (h_lookup_3: lookup_3 c) (h_lookup_4: lookup_4 c)
    (h_lookup_5: lookup_5 c) (h_lookup_6: lookup_6 c) (h_lookup_7: lookup_7 c)
    (h_lookup_8: lookup_8 c) (h_lookup_9: lookup_9 c) (h_lookup_10: lookup_10 c)
    (h_lookup_11: lookup_11 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ col ∈ Finset.Icc 15 24, ∀ row < c.usable_rows, ∃ x0 x1 x2: ℕ,
      x0 < 6 ∧
      x1 < 6 ∧
      x2 < 6 ∧
      c.get_advice col row = input P x0 x1 x2 ∧
      c.get_advice (col+10) row = output P x0 x1 x2
    := by
      intro col h_col
      fin_cases h_col
      . exact lookup_2_normalize_6 c h_lookup_2 h_fixed
      . exact lookup_3_normalize_6 c h_lookup_3 h_fixed
      . exact lookup_4_normalize_6 c h_lookup_4 h_fixed
      . exact lookup_5_normalize_6 c h_lookup_5 h_fixed
      . exact lookup_6_normalize_6 c h_lookup_6 h_fixed
      . exact lookup_7_normalize_6 c h_lookup_7 h_fixed
      . exact lookup_8_normalize_6 c h_lookup_8 h_fixed
      . exact lookup_9_normalize_6 c h_lookup_9 h_fixed
      . exact lookup_10_normalize_6 c h_lookup_10 h_fixed
      . exact lookup_11_normalize_6 c h_lookup_11 h_fixed

end Keccak.Lookups.Normalize_6

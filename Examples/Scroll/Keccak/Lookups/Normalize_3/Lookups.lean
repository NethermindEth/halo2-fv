import Examples.Scroll.Keccak.Lookups.Normalize_3.Input
import Examples.Scroll.Keccak.Lookups.Normalize_3.Output

namespace Keccak.Lookups.Normalize_3

  def transform_table (P: ℕ) (row: ℕ) :=
    if row < 729 then
      (input_by_row P row, output_by_row P row)
    else
      (input_by_row P 0, output_by_row P 0)

  lemma lookup_normalize_3 (col1 col2: ℕ)
    (c: ValidCircuit P P_Prime) (hlookup: ∀ row < c.usable_rows,
      ∃ lookup_row < c.usable_rows,
      (c.get_advice col1 row, c.get_advice col2 row) =
      (c.get_fixed 8 lookup_row, c.get_fixed 9 lookup_row)
    ) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3 x4 x5: ℕ,
      x0 < 3 ∧
      x1 < 3 ∧
      x2 < 3 ∧
      x3 < 3 ∧
      x4 < 3 ∧
      x5 < 3 ∧
      c.get_advice col1 row = input P x0 x1 x2 x3 x4 x5 ∧
      c.get_advice col2 row = output P x0 x1 x2 x3 x4 x5
    := by
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_8_eq_input_of_lt_usable_rows, fixed_func_col_9_eq_output_of_lt_usable_rows, input_by_row, output_by_row]
      use ((if lookup_row < 729 then lookup_row else 0) / 243)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 729 then lookup_row else 0) / 81 % 3)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 729 then lookup_row else 0) / 27 % 3)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 729 then lookup_row else 0) / 9 % 3)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 729 then lookup_row else 0) / 3 % 3)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 729 then lookup_row else 0) % 3)
      apply And.intro
      . split <;> omega
      apply And.intro
      . rfl
      . rfl

  lemma lookup_0_normalize_3 (c: ValidCircuit P P_Prime) (hlookup: lookup_0 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3 x4 x5: ℕ,
      x0 < 3 ∧
      x1 < 3 ∧
      x2 < 3 ∧
      x3 < 3 ∧
      x4 < 3 ∧
      x5 < 3 ∧
      c.get_advice 10 row = input P x0 x1 x2 x3 x4 x5 ∧
      c.get_advice 11 row = output P x0 x1 x2 x3 x4 x5
    := lookup_normalize_3 10 11 c hlookup h_fixed

  lemma lookup_85_normalize_3 (c: ValidCircuit P P_Prime) (hlookup: lookup_85 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3 x4 x5: ℕ,
      x0 < 3 ∧
      x1 < 3 ∧
      x2 < 3 ∧
      x3 < 3 ∧
      x4 < 3 ∧
      x5 < 3 ∧
      c.get_advice 143 row = input P x0 x1 x2 x3 x4 x5 ∧
      c.get_advice 144 row = output P x0 x1 x2 x3 x4 x5
    := lookup_normalize_3 143 144 c hlookup h_fixed

end Keccak.Lookups.Normalize_3

import Examples.Scroll.Keccak.Lookups.Normalize_4.Input
import Examples.Scroll.Keccak.Lookups.Normalize_4.Output

namespace Keccak.Lookups.Normalize_4

  def transform_table (P: ℕ) (row: ℕ) :=
    if row < 256 then
      (input_by_row P row, output_by_row P row)
    else
      (input_by_row P 0, output_by_row P 0)

  lemma apply_transform_table (h: transform_table P row = (x, y)) :
    x = input_by_row P (if row < 256 then row else 0) ∧
    y = output_by_row P (if row < 256 then row else 0)
  := by
    unfold transform_table at h
    by_cases row < 256 <;> simp_all
    rewrite [if_neg (by omega)]
    simp_all

  lemma lookup_normalize_4 (col1 col2: ℕ)
    (c: ValidCircuit P P_Prime) (hlookup: ∀ row < c.usable_rows,
      ∃ lookup_row < c.usable_rows,
      (c.get_advice col1 row, c.get_advice col2 row) =
      (c.get_fixed 10 lookup_row, c.get_fixed 11 lookup_row)
    ) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice col1 row = input P x0 x1 x2 x3 ∧
      c.get_advice col2 row = output P x0 x1 x2 x3
    := by
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_10_eq_input_of_lt_usable_rows, fixed_func_col_11_eq_output_of_lt_usable_rows, input_by_row, output_by_row]
      use ((if lookup_row < 256 then lookup_row else 0) / 64)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 256 then lookup_row else 0) / 16 % 4)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 256 then lookup_row else 0) / 4 % 4)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 256 then lookup_row else 0) % 4)
      apply And.intro
      . split <;> omega
      apply And.intro
      . rfl
      . rfl

  lemma lookup_12_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_12 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 35 row = input P x0 x1 x2 x3 ∧
      c.get_advice 70 row = output P x0 x1 x2 x3
    := lookup_normalize_4 35 70 c hlookup h_fixed

  lemma lookup_13_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_13 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 40 row = input P x0 x1 x2 x3 ∧
      c.get_advice 75 row = output P x0 x1 x2 x3
    := lookup_normalize_4 40 75 c hlookup h_fixed

  lemma lookup_14_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_14 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 50 row = input P x0 x1 x2 x3 ∧
      c.get_advice 85 row = output P x0 x1 x2 x3
    := lookup_normalize_4 50 85 c hlookup h_fixed

  lemma lookup_15_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_15 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 65 row = input P x0 x1 x2 x3 ∧
      c.get_advice 100 row = output P x0 x1 x2 x3
    := lookup_normalize_4 65 100 c hlookup h_fixed

  lemma lookup_16_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_16 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 45 row = input P x0 x1 x2 x3 ∧
      c.get_advice 80 row = output P x0 x1 x2 x3
    := lookup_normalize_4 45 80 c hlookup h_fixed

  lemma lookup_17_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_17 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 55 row = input P x0 x1 x2 x3 ∧
      c.get_advice 90 row = output P x0 x1 x2 x3
    := lookup_normalize_4 55 90 c hlookup h_fixed

  lemma lookup_18_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_18 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 60 row = input P x0 x1 x2 x3 ∧
      c.get_advice 95 row = output P x0 x1 x2 x3
    := lookup_normalize_4 60 95 c hlookup h_fixed

  lemma lookup_19_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_19 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 56 row = input P x0 x1 x2 x3 ∧
      c.get_advice 91 row = output P x0 x1 x2 x3
    := lookup_normalize_4 56 91 c hlookup h_fixed

  lemma lookup_20_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_20 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 61 row = input P x0 x1 x2 x3 ∧
      c.get_advice 96 row = output P x0 x1 x2 x3
    := lookup_normalize_4 61 96 c hlookup h_fixed

  lemma lookup_21_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_21 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 36 row = input P x0 x1 x2 x3 ∧
      c.get_advice 71 row = output P x0 x1 x2 x3
    := lookup_normalize_4 36 71 c hlookup h_fixed

  lemma lookup_22_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_22 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 41 row = input P x0 x1 x2 x3 ∧
      c.get_advice 76 row = output P x0 x1 x2 x3
    := lookup_normalize_4 41 76 c hlookup h_fixed

  lemma lookup_23_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_23 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 51 row = input P x0 x1 x2 x3 ∧
      c.get_advice 86 row = output P x0 x1 x2 x3
    := lookup_normalize_4 51 86 c hlookup h_fixed

  lemma lookup_24_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_24 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 66 row = input P x0 x1 x2 x3 ∧
      c.get_advice 101 row = output P x0 x1 x2 x3
    := lookup_normalize_4 66 101 c hlookup h_fixed

  lemma lookup_25_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_25 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 46 row = input P x0 x1 x2 x3 ∧
      c.get_advice 81 row = output P x0 x1 x2 x3
    := lookup_normalize_4 46 81 c hlookup h_fixed

  lemma lookup_26_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_26 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 47 row = input P x0 x1 x2 x3 ∧
      c.get_advice 82 row = output P x0 x1 x2 x3
    := lookup_normalize_4 47 82 c hlookup h_fixed

  lemma lookup_27_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_27 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 57 row = input P x0 x1 x2 x3 ∧
      c.get_advice 92 row = output P x0 x1 x2 x3
    := lookup_normalize_4 57 92 c hlookup h_fixed

  lemma lookup_28_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_28 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 62 row = input P x0 x1 x2 x3 ∧
      c.get_advice 97 row = output P x0 x1 x2 x3
    := lookup_normalize_4 62 97 c hlookup h_fixed

  lemma lookup_29_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_29 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 37 row = input P x0 x1 x2 x3 ∧
      c.get_advice 72 row = output P x0 x1 x2 x3
    := lookup_normalize_4 37 72 c hlookup h_fixed

  lemma lookup_30_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_30 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 42 row = input P x0 x1 x2 x3 ∧
      c.get_advice 77 row = output P x0 x1 x2 x3
    := lookup_normalize_4 42 77 c hlookup h_fixed

  lemma lookup_31_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_31 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 52 row = input P x0 x1 x2 x3 ∧
      c.get_advice 87 row = output P x0 x1 x2 x3
    := lookup_normalize_4 52 87 c hlookup h_fixed

  lemma lookup_32_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_32 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 67 row = input P x0 x1 x2 x3 ∧
      c.get_advice 102 row = output P x0 x1 x2 x3
    := lookup_normalize_4 67 102 c hlookup h_fixed

  lemma lookup_33_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_33 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 68 row = input P x0 x1 x2 x3 ∧
      c.get_advice 103 row = output P x0 x1 x2 x3
    := lookup_normalize_4 68 103 c hlookup h_fixed

  lemma lookup_34_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_34 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 48 row = input P x0 x1 x2 x3 ∧
      c.get_advice 83 row = output P x0 x1 x2 x3
    := lookup_normalize_4 48 83 c hlookup h_fixed

  lemma lookup_35_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_35 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 58 row = input P x0 x1 x2 x3 ∧
      c.get_advice 93 row = output P x0 x1 x2 x3
    := lookup_normalize_4 58 93 c hlookup h_fixed

  lemma lookup_36_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_36 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 63 row = input P x0 x1 x2 x3 ∧
      c.get_advice 98 row = output P x0 x1 x2 x3
    := lookup_normalize_4 63 98 c hlookup h_fixed

  lemma lookup_37_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_37 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 38 row = input P x0 x1 x2 x3 ∧
      c.get_advice 73 row = output P x0 x1 x2 x3
    := lookup_normalize_4 38 73 c hlookup h_fixed

  lemma lookup_38_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_38 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 43 row = input P x0 x1 x2 x3 ∧
      c.get_advice 78 row = output P x0 x1 x2 x3
    := lookup_normalize_4 43 78 c hlookup h_fixed

  lemma lookup_39_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_39 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 53 row = input P x0 x1 x2 x3 ∧
      c.get_advice 88 row = output P x0 x1 x2 x3
    := lookup_normalize_4 53 88 c hlookup h_fixed

  lemma lookup_40_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_40 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 54 row = input P x0 x1 x2 x3 ∧
      c.get_advice 89 row = output P x0 x1 x2 x3
    := lookup_normalize_4 54 89 c hlookup h_fixed

  lemma lookup_41_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_41 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 69 row = input P x0 x1 x2 x3 ∧
      c.get_advice 104 row = output P x0 x1 x2 x3
    := lookup_normalize_4 69 104 c hlookup h_fixed

  lemma lookup_42_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_42 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 49 row = input P x0 x1 x2 x3 ∧
      c.get_advice 84 row = output P x0 x1 x2 x3
    := lookup_normalize_4 49 84 c hlookup h_fixed

  lemma lookup_43_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_43 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 59 row = input P x0 x1 x2 x3 ∧
      c.get_advice 94 row = output P x0 x1 x2 x3
    := lookup_normalize_4 59 94 c hlookup h_fixed

  lemma lookup_44_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_44 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 64 row = input P x0 x1 x2 x3 ∧
      c.get_advice 99 row = output P x0 x1 x2 x3
    := lookup_normalize_4 64 99 c hlookup h_fixed

  lemma lookup_45_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_45 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 39 row = input P x0 x1 x2 x3 ∧
      c.get_advice 74 row = output P x0 x1 x2 x3
    := lookup_normalize_4 39 74 c hlookup h_fixed

  lemma lookup_46_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_46 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 44 row = input P x0 x1 x2 x3 ∧
      c.get_advice 79 row = output P x0 x1 x2 x3
    := lookup_normalize_4 44 79 c hlookup h_fixed

  lemma lookup_normalize_4_input (col : ℕ)
    (c: ValidCircuit P P_Prime) (hlookup: ∀ row < c.usable_rows,
      ∃ lookup_row < c.usable_rows,
      (c.get_advice col row) =
      (c.get_fixed 10 lookup_row)
    ) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice col row = input P x0 x1 x2 x3
    := by
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_10_eq_input_of_lt_usable_rows, fixed_func_col_11_eq_output_of_lt_usable_rows, input_by_row, output_by_row]
      use ((if lookup_row < 256 then lookup_row else 0) / 64)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 256 then lookup_row else 0) / 16 % 4)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 256 then lookup_row else 0) / 4 % 4)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 256 then lookup_row else 0) % 4)
      apply And.intro
      . split <;> omega
      rfl

  lemma lookup_47_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_47 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 140 row = input P x0 x1 x2 x3
    := lookup_normalize_4_input 140 c hlookup h_fixed

  lemma lookup_48_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_48 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 141 row = input P x0 x1 x2 x3
    := lookup_normalize_4_input 141 c hlookup h_fixed

  lemma lookup_49_normalize_4 (c: ValidCircuit P P_Prime) (hlookup: lookup_49 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 4 ∧
      x1 < 4 ∧
      x2 < 4 ∧
      x3 < 4 ∧
      c.get_advice 142 row = input P x0 x1 x2 x3
    := lookup_normalize_4_input 142 c hlookup h_fixed

  def normalize_4_column_pairs := [
    (35, 70),
    (40, 75),
    (50, 85),
    (65, 100),
    (45, 80),
    (55, 90),
    (60, 95),
    (56, 91),
    (61, 96),
    (36, 71),
    (41, 76),
    (51, 86),
    (66, 101),
    (46, 81),
    (47, 82),
    (57, 92),
    (62, 97),
    (37, 72),
    (42, 77),
    (52, 87),
    (67, 102),
    (68, 103),
    (48, 83),
    (58, 93),
    (63, 98),
    (38, 73),
    (43, 78),
    (53, 88),
    (54, 89),
    (69, 104),
    (49, 84),
    (59, 94),
    (64, 99),
    (39, 74),
    (44, 79)
  ]

  lemma lookup_12_to_46_normalize_4 (c: ValidCircuit P P_Prime)
    (h_lookup_12: lookup_12 c)
    (h_lookup_13: lookup_13 c)
    (h_lookup_14: lookup_14 c)
    (h_lookup_15: lookup_15 c)
    (h_lookup_16: lookup_16 c)
    (h_lookup_17: lookup_17 c)
    (h_lookup_18: lookup_18 c)
    (h_lookup_19: lookup_19 c)
    (h_lookup_20: lookup_20 c)
    (h_lookup_21: lookup_21 c)
    (h_lookup_22: lookup_22 c)
    (h_lookup_23: lookup_23 c)
    (h_lookup_24: lookup_24 c)
    (h_lookup_25: lookup_25 c)
    (h_lookup_26: lookup_26 c)
    (h_lookup_27: lookup_27 c)
    (h_lookup_28: lookup_28 c)
    (h_lookup_29: lookup_29 c)
    (h_lookup_30: lookup_30 c)
    (h_lookup_31: lookup_31 c)
    (h_lookup_32: lookup_32 c)
    (h_lookup_33: lookup_33 c)
    (h_lookup_34: lookup_34 c)
    (h_lookup_35: lookup_35 c)
    (h_lookup_36: lookup_36 c)
    (h_lookup_37: lookup_37 c)
    (h_lookup_38: lookup_38 c)
    (h_lookup_39: lookup_39 c)
    (h_lookup_40: lookup_40 c)
    (h_lookup_41: lookup_41 c)
    (h_lookup_42: lookup_42 c)
    (h_lookup_43: lookup_43 c)
    (h_lookup_44: lookup_44 c)
    (h_lookup_45: lookup_45 c)
    (h_lookup_46: lookup_46 c)
    (h_fixed: c.1.Fixed = fixed_func c):
      ∀ pair ∈ normalize_4_column_pairs,
      ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
        x0 < 4 ∧
        x1 < 4 ∧
        x2 < 4 ∧
        x3 < 4 ∧
        c.get_advice pair.1 row = input P x0 x1 x2 x3 ∧
        c.get_advice pair.2 row = output P x0 x1 x2 x3
    := by
      intro pair h_pair
      fin_cases h_pair
      . exact lookup_12_normalize_4 c h_lookup_12 h_fixed
      . exact lookup_13_normalize_4 c h_lookup_13 h_fixed
      . exact lookup_14_normalize_4 c h_lookup_14 h_fixed
      . exact lookup_15_normalize_4 c h_lookup_15 h_fixed
      . exact lookup_16_normalize_4 c h_lookup_16 h_fixed
      . exact lookup_17_normalize_4 c h_lookup_17 h_fixed
      . exact lookup_18_normalize_4 c h_lookup_18 h_fixed
      . exact lookup_19_normalize_4 c h_lookup_19 h_fixed
      . exact lookup_20_normalize_4 c h_lookup_20 h_fixed
      . exact lookup_21_normalize_4 c h_lookup_21 h_fixed
      . exact lookup_22_normalize_4 c h_lookup_22 h_fixed
      . exact lookup_23_normalize_4 c h_lookup_23 h_fixed
      . exact lookup_24_normalize_4 c h_lookup_24 h_fixed
      . exact lookup_25_normalize_4 c h_lookup_25 h_fixed
      . exact lookup_26_normalize_4 c h_lookup_26 h_fixed
      . exact lookup_27_normalize_4 c h_lookup_27 h_fixed
      . exact lookup_28_normalize_4 c h_lookup_28 h_fixed
      . exact lookup_29_normalize_4 c h_lookup_29 h_fixed
      . exact lookup_30_normalize_4 c h_lookup_30 h_fixed
      . exact lookup_31_normalize_4 c h_lookup_31 h_fixed
      . exact lookup_32_normalize_4 c h_lookup_32 h_fixed
      . exact lookup_33_normalize_4 c h_lookup_33 h_fixed
      . exact lookup_34_normalize_4 c h_lookup_34 h_fixed
      . exact lookup_35_normalize_4 c h_lookup_35 h_fixed
      . exact lookup_36_normalize_4 c h_lookup_36 h_fixed
      . exact lookup_37_normalize_4 c h_lookup_37 h_fixed
      . exact lookup_38_normalize_4 c h_lookup_38 h_fixed
      . exact lookup_39_normalize_4 c h_lookup_39 h_fixed
      . exact lookup_40_normalize_4 c h_lookup_40 h_fixed
      . exact lookup_41_normalize_4 c h_lookup_41 h_fixed
      . exact lookup_42_normalize_4 c h_lookup_42 h_fixed
      . exact lookup_43_normalize_4 c h_lookup_43 h_fixed
      . exact lookup_44_normalize_4 c h_lookup_44 h_fixed
      . exact lookup_45_normalize_4 c h_lookup_45 h_fixed
      . exact lookup_46_normalize_4 c h_lookup_46 h_fixed


end Keccak.Lookups.Normalize_4

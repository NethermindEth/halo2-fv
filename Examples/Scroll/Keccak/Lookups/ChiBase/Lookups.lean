import Examples.Scroll.Keccak.Lookups.ChiBase.Input
import Examples.Scroll.Keccak.Lookups.ChiBase.Output

namespace Keccak.Lookups.ChiBase

  lemma lookup_chi_base (x y: ℕ → ZMod P)
    (c: ValidCircuit P P_Prime) (hlookup: ∀ row < c.usable_rows,
      ∃ lookup_row < c.usable_rows,
      (x row , y row) =
      (c.get_fixed 14 lookup_row, c.get_fixed 15 lookup_row)
    ) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      x row = input P x0 x1 x2 x3 ∧
      y row = output P x0 x1 x2 x3
    := by
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_14_eq_input_of_lt_usable_rows, fixed_func_col_15_eq_output_of_lt_usable_rows, input_by_row, output_by_row]
      use ((if lookup_row < 625 then lookup_row else 0) / 125 % 5)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 625 then lookup_row else 0) / 25 % 5)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 625 then lookup_row else 0) / 5 % 5)
      apply And.intro
      . split <;> omega
      use ((if lookup_row < 625 then lookup_row else 0) % 5)
      apply And.intro
      . split <;> omega
      apply And.intro
      . rfl
      . rfl

  lemma lookup_50_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_50 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 70 row) + c.get_advice 71 row - c.get_advice 72 row = input P x0 x1 x2 x3 ∧
      c.get_advice 105 row = output P x0 x1 x2 x3
    := by
      unfold lookup_50 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_51_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_51 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 71 row) + c.get_advice 72 row - c.get_advice 73 row = input P x0 x1 x2 x3 ∧
      c.get_advice 106 row = output P x0 x1 x2 x3
    := by
      unfold lookup_51 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_52_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_52 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 72 row) + c.get_advice 73 row - c.get_advice 74 row = input P x0 x1 x2 x3 ∧
      c.get_advice 107 row = output P x0 x1 x2 x3
    := by
      unfold lookup_52 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_53_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_53 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 73 row) + c.get_advice 74 row - c.get_advice 70 row = input P x0 x1 x2 x3 ∧
      c.get_advice 108 row = output P x0 x1 x2 x3
    := by
      unfold lookup_53 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_54_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_54 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 74 row) + c.get_advice 70 row - c.get_advice 71 row = input P x0 x1 x2 x3 ∧
      c.get_advice 109 row = output P x0 x1 x2 x3
    := by
      unfold lookup_54 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_55_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_55 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 75 row) + c.get_advice 76 row - c.get_advice 77 row = input P x0 x1 x2 x3 ∧
      c.get_advice 110 row = output P x0 x1 x2 x3
    := by
      unfold lookup_55 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_56_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_56 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 76 row) + c.get_advice 77 row - c.get_advice 78 row = input P x0 x1 x2 x3 ∧
      c.get_advice 111 row = output P x0 x1 x2 x3
    := by
      unfold lookup_56 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_57_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_57 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 77 row) + c.get_advice 78 row - c.get_advice 79 row = input P x0 x1 x2 x3 ∧
      c.get_advice 112 row = output P x0 x1 x2 x3
    := by
      unfold lookup_57 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_58_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_58 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 78 row) + c.get_advice 79 row - c.get_advice 75 row = input P x0 x1 x2 x3 ∧
      c.get_advice 113 row = output P x0 x1 x2 x3
    := by
      unfold lookup_58 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_59_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_59 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 79 row) + c.get_advice 75 row - c.get_advice 76 row = input P x0 x1 x2 x3 ∧
      c.get_advice 114 row = output P x0 x1 x2 x3
    := by
      unfold lookup_59 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_60_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_60 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 80 row) + c.get_advice 81 row - c.get_advice 82 row = input P x0 x1 x2 x3 ∧
      c.get_advice 115 row = output P x0 x1 x2 x3
    := by
      unfold lookup_60 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_61_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_61 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 81 row) + c.get_advice 82 row - c.get_advice 83 row = input P x0 x1 x2 x3 ∧
      c.get_advice 116 row = output P x0 x1 x2 x3
    := by
      unfold lookup_61 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_62_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_62 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 82 row) + c.get_advice 83 row - c.get_advice 84 row = input P x0 x1 x2 x3 ∧
      c.get_advice 117 row = output P x0 x1 x2 x3
    := by
      unfold lookup_62 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_63_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_63 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 83 row) + c.get_advice 84 row - c.get_advice 80 row = input P x0 x1 x2 x3 ∧
      c.get_advice 118 row = output P x0 x1 x2 x3
    := by
      unfold lookup_63 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_64_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_64 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 84 row) + c.get_advice 80 row - c.get_advice 81 row = input P x0 x1 x2 x3 ∧
      c.get_advice 119 row = output P x0 x1 x2 x3
    := by
      unfold lookup_64 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_65_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_65 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 85 row) + c.get_advice 86 row - c.get_advice 87 row = input P x0 x1 x2 x3 ∧
      c.get_advice 120 row = output P x0 x1 x2 x3
    := by
      unfold lookup_65 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_66_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_66 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 86 row) + c.get_advice 87 row - c.get_advice 88 row = input P x0 x1 x2 x3 ∧
      c.get_advice 121 row = output P x0 x1 x2 x3
    := by
      unfold lookup_66 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_67_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_67 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 87 row) + c.get_advice 88 row - c.get_advice 89 row = input P x0 x1 x2 x3 ∧
      c.get_advice 122 row = output P x0 x1 x2 x3
    := by
      unfold lookup_67 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_68_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_68 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 88 row) + c.get_advice 89 row - c.get_advice 85 row = input P x0 x1 x2 x3 ∧
      c.get_advice 123 row = output P x0 x1 x2 x3
    := by
      unfold lookup_68 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_69_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_69 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 89 row) + c.get_advice 85 row - c.get_advice 86 row = input P x0 x1 x2 x3 ∧
      c.get_advice 124 row = output P x0 x1 x2 x3
    := by
      unfold lookup_69 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_70_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_70 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 90 row) + c.get_advice 91 row - c.get_advice 92 row = input P x0 x1 x2 x3 ∧
      c.get_advice 125 row = output P x0 x1 x2 x3
    := by
      unfold lookup_70 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_71_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_71 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 91 row) + c.get_advice 92 row - c.get_advice 93 row = input P x0 x1 x2 x3 ∧
      c.get_advice 126 row = output P x0 x1 x2 x3
    := by
      unfold lookup_71 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_72_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_72 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 92 row) + c.get_advice 93 row - c.get_advice 94 row = input P x0 x1 x2 x3 ∧
      c.get_advice 127 row = output P x0 x1 x2 x3
    := by
      unfold lookup_72 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_73_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_73 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 93 row) + c.get_advice 94 row - c.get_advice 90 row = input P x0 x1 x2 x3 ∧
      c.get_advice 128 row = output P x0 x1 x2 x3
    := by
      unfold lookup_73 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_74_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_74 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 94 row) + c.get_advice 90 row - c.get_advice 91 row = input P x0 x1 x2 x3 ∧
      c.get_advice 129 row = output P x0 x1 x2 x3
    := by
      unfold lookup_74 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_75_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_75 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 95 row) + c.get_advice 96 row - c.get_advice 97 row = input P x0 x1 x2 x3 ∧
      c.get_advice 130 row = output P x0 x1 x2 x3
    := by
      unfold lookup_75 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_76_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_76 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 96 row) + c.get_advice 97 row - c.get_advice 98 row = input P x0 x1 x2 x3 ∧
      c.get_advice 131 row = output P x0 x1 x2 x3
    := by
      unfold lookup_76 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_77_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_77 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 97 row) + c.get_advice 98 row - c.get_advice 99 row = input P x0 x1 x2 x3 ∧
      c.get_advice 132 row = output P x0 x1 x2 x3
    := by
      unfold lookup_77 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_78_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_78 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 98 row) + c.get_advice 99 row - c.get_advice 95 row = input P x0 x1 x2 x3 ∧
      c.get_advice 133 row = output P x0 x1 x2 x3
    := by
      unfold lookup_78 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_79_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_79 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 99 row) + c.get_advice 95 row - c.get_advice 96 row = input P x0 x1 x2 x3 ∧
      c.get_advice 134 row = output P x0 x1 x2 x3
    := by
      unfold lookup_79 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_80_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_80 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 100 row) + c.get_advice 101 row - c.get_advice 102 row = input P x0 x1 x2 x3 ∧
      c.get_advice 135 row = output P x0 x1 x2 x3
    := by
      unfold lookup_80 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_81_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_81 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 101 row) + c.get_advice 102 row - c.get_advice 103 row = input P x0 x1 x2 x3 ∧
      c.get_advice 136 row = output P x0 x1 x2 x3
    := by
      unfold lookup_81 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_82_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_82 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 102 row) + c.get_advice 103 row - c.get_advice 104 row = input P x0 x1 x2 x3 ∧
      c.get_advice 137 row = output P x0 x1 x2 x3
    := by
      unfold lookup_82 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_83_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_83 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 103 row) + c.get_advice 104 row - c.get_advice 100 row = input P x0 x1 x2 x3 ∧
      c.get_advice 138 row = output P x0 x1 x2 x3
    := by
      unfold lookup_83 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

  lemma lookup_84_chi_base (c: ValidCircuit P P_Prime) (hlookup: lookup_84 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x0 x1 x2 x3: ℕ,
      x0 < 5 ∧
      x1 < 5 ∧
      x2 < 5 ∧
      x3 < 5 ∧
      1755 - 2*(c.get_advice 104 row) + c.get_advice 100 row - c.get_advice 101 row = input P x0 x1 x2 x3 ∧
      c.get_advice 139 row = output P x0 x1 x2 x3
    := by
      unfold lookup_84 at hlookup
      intro row hrow
      replace hlookup := lookup_chi_base (λ row => _) _ c hlookup h_fixed row hrow
      obtain ⟨x0, x1, x2, x3, hx0, hx1, hx2, hx3, ⟨hlookup_input, hlookup_output⟩⟩ := hlookup
      use x0, x1, x2, x3
      simp_all [sub_eq_neg_add, add_comm]

end Keccak.Lookups.ChiBase

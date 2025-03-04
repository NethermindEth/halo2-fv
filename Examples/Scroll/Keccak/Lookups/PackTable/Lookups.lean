import Examples.Scroll.Keccak.Lookups.PackTable.Packed
import Examples.Scroll.Keccak.Lookups.PackTable.Unpacked

namespace Keccak.Lookups.PackTable

  lemma lookup_pack_table (col1 col2: ℕ)
    (c: ValidCircuit P P_Prime) (hlookup: ∀ row < c.usable_rows,
      ∃ lookup_row < c.usable_rows,
      (c.get_advice col1 row, c.get_advice col2 row) =
      (c.get_fixed 17 lookup_row, c.get_fixed 16 lookup_row)
    ) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x: ℕ,
      x < 256 ∧
      c.get_advice col1 row = pack P (into_bits [x]) ∧
      c.get_advice col2 row = x
    := by
      intro row hrow
      obtain ⟨lookup_row, ⟨hlookup_row, hlookup⟩⟩ := hlookup row hrow
      by_cases hlookup_row_range: lookup_row < 256
      all_goals simp_all [ValidCircuit.get_fixed, fixed_func, fixed_func_col_16_eq_unpacked_of_lt_usable_rows, fixed_func_col_17_eq_packed_of_lt_usable_rows, pack, pack_with_base, keccak_constants, into_bits, loop_8]
      . use lookup_row
      . use 0
        norm_num

  lemma lookup_1_pack_table (c: ValidCircuit P P_Prime) (hlookup: lookup_1 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x: ℕ,
      x < 256 ∧
      c.get_advice 12 row = pack P (into_bits [x]) ∧
      c.get_advice 13 row = x
    := lookup_pack_table 12 13 c hlookup h_fixed

  lemma lookup_86_pack_table (c: ValidCircuit P P_Prime) (hlookup: lookup_86 c) (h_fixed: c.1.Fixed = fixed_func c):
    ∀ row < c.usable_rows, ∃ x: ℕ,
      x < 256 ∧
      c.get_advice 146 row = pack P (into_bits [x]) ∧
      c.get_advice 147 row = x
    := lookup_pack_table 146 147 c hlookup h_fixed

end Keccak.Lookups.PackTable

import Examples.Scroll.Keccak.Lookups.PackTable.Packed
import Examples.Scroll.Keccak.Lookups.PackTable.Unpacked
import Examples.Util

namespace Keccak.Lookups.PackTable

  def transform_table (P: ℕ) (row: ℕ) :=
    if row < 256 then
      (pack P (into_bits [row]), (row: ZMod P))
    else
      (pack P (into_bits [0]), (0: ZMod P))

  lemma apply_transform_table
    (h: ∃ lookup_row, Lookups.PackTable.transform_table P lookup_row = (x, y))
    (h_P: P ≥ 256)
  :
    x = pack P (into_bits [y.val])
  := by
    obtain ⟨lookup_row, h_lookup_row⟩ := h
    unfold transform_table at h_lookup_row
    by_cases h: lookup_row < 256
    . simp [h] at h_lookup_row
      rewrite [←h_lookup_row.2]
      simp
      rewrite [Nat.mod_eq_of_lt (by omega)]
      rw [h_lookup_row.1]
    . simp [h] at h_lookup_row
      rewrite [←h_lookup_row.2]
      simp
      rw [h_lookup_row.1]

  lemma apply_transform_table_input_range [NeZero P]
    (h: ∃ lookup_row, Lookups.PackTable.transform_table P lookup_row = (x, y))
  :
    x.val ≤ 0b001001001001001001001001
  := by
    obtain ⟨lookup_row, h_lookup_row⟩ := h
    by_cases h_range: lookup_row < 256
    . simp [
        transform_table, h_range
      ] at h_lookup_row
      rewrite [←h_lookup_row.1]
      simp [
        into_bits, list_ops,
        pack, keccak_constants,
        pack_with_base, ZMod.val_add,
        ZMod.val_mul
      ]
      rewrite [zmod_val_ofNat]
      apply le_trans (Nat.mod_le _ _)
      have h_le (x: ℕ): x % 2 ≤ 1 := by omega
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001001001001001001001) _ (Nat.mod_le 8 P)
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001001001001001001) _ (Nat.mod_le 8 P)
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001001001001001) _ (Nat.mod_le 8 P)
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001001001001) _ (Nat.mod_le 8 P)
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001001001) _ (Nat.mod_le 8 P)
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001001) _ (Nat.mod_le 8 P)
      apply add_le_add _ (h_le _)
      apply Nat.mul_le_mul (n₂ := 0b001) _ (Nat.mod_le 8 P)
      exact h_le _
    . simp [
        transform_table, h_range, into_bits,
        pack, keccak_constants
      ] at h_lookup_row
      have ⟨h_lookup_row, _⟩ := h_lookup_row
      simp [pack_with_base] at h_lookup_row
      rewrite [←h_lookup_row]
      simp

  lemma apply_transform_table_output_range
    (x y: ZMod P)
    (h: ∃ lookup_row, Lookups.PackTable.transform_table P lookup_row = (x, y))
    (h_P: P ≥ 256)
  :
    y.val < 256
  := by
    unfold Lookups.PackTable.transform_table at h
    obtain ⟨row, h_row⟩ := h
    split_ifs at h_row
    . simp at h_row
      rewrite [←h_row.2]
      simp
      rewrite [Nat.mod_eq_of_lt (by omega)]
      assumption
    . simp at h_row
      rewrite [←h_row.2]
      simp

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

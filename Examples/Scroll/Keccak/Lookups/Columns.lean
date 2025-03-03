import Examples.Scroll.Keccak.Extraction

namespace Keccak.Lookups
  def normalize_3 (c: ValidCircuit P P_Prime) (row: ℕ) := (c.get_fixed 8 row, c.get_fixed 9 row)
  def normalize_4 (c: ValidCircuit P P_Prime) (row: ℕ) := (c.get_fixed 10 row, c.get_fixed 11 row)
  def normalize_6 (c: ValidCircuit P P_Prime) (row: ℕ) := (c.get_fixed 12 row, c.get_fixed 13 row)
  def chi_base (c: ValidCircuit P P_Prime) (row: ℕ) := (c.get_fixed 14 row, c.get_fixed 15 row)
  def pack_table (c: ValidCircuit P P_Prime) (row: ℕ) := (c.get_fixed 16 row, c.get_fixed 17 row)
end Keccak.Lookups

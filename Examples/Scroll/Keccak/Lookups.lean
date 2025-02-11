import Examples.Scroll.Keccak.Extraction

namespace Keccak

  namespace Lookups
    def normalize_3 (c: ValidCircuit P P_Prime) (row: ℕ) := (c.get_fixed 8 row, c.get_fixed 9 row)
  end Lookups

end Keccak

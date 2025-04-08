import Examples.Scroll.Keccak.Soundness.Theta
import Examples.Scroll.Keccak.Soundness.Normalize

namespace Keccak.Soundness

  lemma rotation_normalized:
    ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft BIT_COUNT).toNat =
    Normalize.normalize_unpacked (
      ((BitVec.ofNat 192 (Normalize.normalize_unpacked x 64)).rotateLeft BIT_COUNT).toNat
    ) 64
  := by
    rewrite [
      ←Normalize.normalize_unpacked_ofNat_toNat (show 192 = BIT_COUNT*64 by simp [keccak_constants]),
      Normalize.normalize_unpacked_toNat
    ]
    rewrite [
      BitVec.ofNat_toNat,
      Normalize.normalize_unpacked_toNat,
      ←BitVec.toNat_eq
    ]
    simp only [keccak_constants, Nat.reduceMul, Normalize.mask_bitvec]
    bv_decide

  lemma os_range {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P):
    (os c round i j).val < 2^192
  := by
    rewrite [
      os_theta h_meets_constraints h_round h_P,
      rotation_normalized
    ]
    apply lt_of_le_of_lt
      (add_le_add
        (s_range h_meets_constraints h_round (by omega) (i := i) (j := j))
        (add_le_add Normalize.normalize_unpacked_64_le_mask Normalize.normalize_unpacked_64_le_mask))
    simp [Normalize.mask]
end Keccak.Soundness

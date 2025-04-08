import Mathlib.Data.ZMod.Basic

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Lookups.Normalize_4.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.PiPartsRangeCheck
import Examples.Scroll.Keccak.ProgramProofs.RhoByPi
import Examples.Scroll.Keccak.ProgramProofs.Theta
import Examples.Scroll.Keccak.Soundness.Lookups.Normalize_4
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.PiPartsRange
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak.Soundness

  lemma cell_370_rot_parts {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24):
    2^9 * cell_manager c round 1611 + cell_manager c round 1610 =
    cell_manager c round 370
  := by
    have ⟨_, h_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 2
    simp [
      keccak_constants, word_parts_known, list_ops,
      s_parts_cell_offsets.eq_def, pi_region_start.eq_def, get_rotate_count.eq_def, target_part_sizes_known,
      SplitUniform.rot_parts.eq_def, rho_pi_chi_cells
    ] at h_rot_parts
    simp [h_rot_parts, mul_comm, add_comm]

end Keccak.Soundness

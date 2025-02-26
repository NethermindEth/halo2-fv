import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.Padding
  lemma gate_137_last_is_padding_zero_on_absorb_rows (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_137 c) (h_n: 311 < c.n):
    ∀ round, (round = 0 ∨ round = 25) →
    is_paddings c round 7 = 0
  := by
    unfold gate_137 at hgate
    intro round hround
    replace hgate := hgate (12*round)
    simp only [ValidCircuit.get_fixed, h_fixed, Selectors.q_absorb_at_start_or_end, one_mul, hround] at hgate
    have h_n': (12*round)+11 < c.n := by cases hround <;> linarith
    simp [to_cell_manager, h_n', zero_mul] at hgate
    rewrite [←hgate]
    rfl
end Keccak.Gates.Padding

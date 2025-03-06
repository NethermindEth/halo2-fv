import Examples.Scroll.Keccak.Gates.Padding.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma is_padding_boolean_of_meets_constraints (h: meets_constraints c):
    ∀ round ≤ 25, ∀ idx,
      is_padding_boolean c round idx
    := by
      intro round h_round idx
      unfold is_padding_boolean
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      fin_cases idx
      . exact Gates.Padding.gate_129_is_padding_boolean c h_fixed (gate_129_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_130_is_padding_boolean c h_fixed (gate_130_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_131_is_padding_boolean c h_fixed (gate_131_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_132_is_padding_boolean c h_fixed (gate_132_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_133_is_padding_boolean c h_fixed (gate_133_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_134_is_padding_boolean c h_fixed (gate_134_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_135_is_padding_boolean c h_fixed (gate_135_of_meets_constraints h) (by omega) round h_round
      . exact Gates.Padding.gate_136_is_padding_boolean c h_fixed (gate_136_of_meets_constraints h) (by omega) round h_round

  lemma last_is_padding_zero_on_absorb_rows_of_meets_constraints (h: meets_constraints c):
    ∀ round, last_is_padding_zero_on_absorb_rows c round
  := by
    intro round
    simp [last_is_padding_zero_on_absorb_rows]
    intro h_round
    have h_n := n_range_of_meets_constraints h
    exact Gates.Padding.gate_137_last_is_padding_zero_on_absorb_rows
      c
      (fixed_of_meets_constraints h)
      (gate_137_of_meets_constraints h)
      (by omega)
      round
      h_round

  lemma padding_step_boolean_of_meets_constraints (h: meets_constraints c):
    ∀ round, padding_step_boolean c round
  := by
    intro round
    simp [padding_step_boolean]
    intro idx
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    fin_cases idx
    . exact Gates.Padding.gate_138_padding_step_boolean c h_fixed (gate_138_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_140_padding_step_boolean c h_fixed (gate_140_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_142_padding_step_boolean c h_fixed (gate_142_of_meets_constraints h) round h_round.2 h_round.1
    . exact Gates.Padding.gate_144_padding_step_boolean c h_fixed (gate_144_of_meets_constraints h) round h_round.2 h_round.1
    . exact Gates.Padding.gate_146_padding_step_boolean c h_fixed (gate_146_of_meets_constraints h) round h_round.2 h_round.1
    . exact Gates.Padding.gate_148_padding_step_boolean c h_fixed (gate_148_of_meets_constraints h) round h_round.2 h_round.1
    . exact Gates.Padding.gate_150_padding_step_boolean c h_fixed (gate_150_of_meets_constraints h) round h_round.2 h_round.1
    . exact Gates.Padding.gate_152_padding_step_boolean c h_fixed (gate_152_of_meets_constraints h) round h_round.2 h_round.1

  lemma padding_start_intermediate_byte_of_meets_constraints (h: meets_constraints c):
    ∀ round, padding_start_intermediate_byte c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [padding_start_intermediate_byte]
    intro idx h_idx
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    fin_cases idx
    . exact Gates.Padding.gate_139_padding_start_intermediate_byte c h_fixed (gate_139_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_141_padding_start_intermediate_byte c h_fixed (gate_141_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_143_padding_start_intermediate_byte c h_fixed (gate_143_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_145_padding_start_intermediate_byte c h_fixed (gate_145_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_147_padding_start_intermediate_byte c h_fixed (gate_147_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_149_padding_start_intermediate_byte c h_fixed (gate_149_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . exact Gates.Padding.gate_151_padding_start_intermediate_byte c h_fixed (gate_151_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    . contradiction

  lemma padding_start_intermediate_byte_of_meets_constraints_last_byte (h: meets_constraints c):
    ∀ round, padding_start_intermediate_byte_last_byte c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [padding_start_intermediate_byte_last_byte]
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    exact Gates.Padding.gate_153_padding_start_intermediate_byte_last_byte c h_fixed (gate_153_of_meets_constraints h) (by omega) round h_round.2 h_round.1

  lemma padding_start_end_byte_of_meets_constraints (h: meets_constraints c):
    padding_start_end_byte c
  := by
    simp [padding_start_end_byte]
    have h_fixed := fixed_of_meets_constraints h
    exact Gates.Padding.gate_154_padding_start_intermediate_byte_last_byte c h_fixed (gate_154_of_meets_constraints h)

end Keccak.Proofs

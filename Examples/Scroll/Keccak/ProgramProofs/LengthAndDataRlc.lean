import Examples.Scroll.Keccak.Gates.LengthAndDataRlc.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.FirstRow
import Examples.Scroll.Keccak.ProgramProofs.InputChecks
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma update_length_of_meets_constraints (h: meets_constraints c):
    ∀ round, update_length c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [update_length]
    have h_fixed := (fixed_of_meets_constraints h)
    have h_n := n_range_of_meets_constraints h
    have h_is_final_disabled_on_first_row := (is_final_disabled_on_first_row_of_meets_constraints h)
    have := Gates.LengthAndDataRlc.gate_155_update_length
      c
      h_fixed
      (gate_155_of_meets_constraints h)
      h_is_final_disabled_on_first_row
      (boolean_is_final_of_meets_constraints h)
      (by omega)
      round
      h_round.2
      h_round.1
    by_cases h_start_new_hash: start_new_hash c (get_num_rows_per_round * (round-1))
    . split_ands
      . simp [h_start_new_hash]
        unfold start_new_hash at h_start_new_hash
        cases h_start_new_hash with
          | inl h_start_new_hash =>
            simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_1_q_first, Selectors.q_first, keccak_constants] at h_start_new_hash
            rewrite [if_pos, zmod_not_zero_eq_one] at h_start_new_hash
            . simp at h_start_new_hash
              unfold is_final_disabled_on_first_row at h_is_final_disabled_on_first_row
              have h_round : round = 1 := by omega
              simp_all [keccak_constants]
            . assumption
            . omega
          | inr h_start_new_hash =>
            unfold is_final_disabled_on_first_row at h_is_final_disabled_on_first_row
            simp_all [keccak_constants]
            cases this with
              | inl this => assumption
              | inr this =>
                have h_contr := this.1.2.symm
                rewrite [zmod_not_zero_eq_one] at h_contr
                . contradiction
                . assumption
      . intro h_contr; contradiction
    . simp [h_start_new_hash]
      unfold start_new_hash at h_start_new_hash
      simp at h_start_new_hash
      simp_all [keccak_constants]
      have h_boolean_is_final := boolean_is_final_of_meets_constraints h
      unfold boolean_is_final at h_boolean_is_final
      specialize h_boolean_is_final (round-1) (by omega)
      cases h_boolean_is_final with
        | inl h_boolean_is_final =>
          simp_all [ValidCircuit.get_fixed, Selectors.fixed_1_q_first, Selectors.q_first]
          rewrite [if_pos (by omega)] at h_start_new_hash
          replace h_start_new_hash := h_start_new_hash.1.1
          cases this with
            | inl this => omega
            | inr this => exact this.2
        | inr h_boolean_is_final => simp_all

  lemma initial_data_rlc_of_meets_constraints (h: meets_constraints c):
    ∀ round, initial_data_rlc c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [initial_data_rlc]
    have h_is_final_disabled_on_first_row := is_final_disabled_on_first_row_of_meets_constraints h
    have h_is_final_bool:= boolean_is_final_of_meets_constraints h
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    have h_gate := Gates.LengthAndDataRlc.gate_156_initial_data_rlc
      c
      h_fixed
      (gate_156_of_meets_constraints h)
      h_is_final_disabled_on_first_row
      h_is_final_bool
      (by omega)
      round
      h_round.2
      h_round.1
    cases h_gate with
      | inl h_gate =>
        simp_all [start_new_hash, keccak_constants]
        intro h_start h_is_final
        cases h_gate.1 with
          | inl h_round => simp_all [ValidCircuit.get_fixed, Selectors.fixed_1_q_first, Selectors.q_first_zero]
          | inr h_is_final' => simp_all
      | inr hgate =>
        simp_all [start_new_hash, keccak_constants]
        intro h_first
        simp_all [ValidCircuit.get_fixed, Selectors.fixed_1_q_first, Selectors.q_first]
        have h_round : ¬round - 1 = 0 := by omega
        simp_all
        rewrite [if_pos (by omega)] at h_first
        cases h_first with
          | inl h_contr =>
            rewrite [zmod_not_zero_eq_one] at h_contr
            . contradiction
            . assumption
          | inr h_contr =>
            rewrite [zmod_not_zero_eq_one] at h_contr
            . contradiction
            . assumption

  lemma intermediate_data_rlc_of_meets_constraints (h: meets_constraints c):
    ∀ round, intermediate_data_rlc c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [intermediate_data_rlc]
    intro idx
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    fin_cases idx
    exact Gates.LengthAndDataRlc.gate_157_intermediate_data_rlc c h_fixed (gate_157_of_meets_constraints h) (gate_129_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_158_intermediate_data_rlc c h_fixed (gate_158_of_meets_constraints h) (gate_130_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_159_intermediate_data_rlc c h_fixed (gate_159_of_meets_constraints h) (gate_131_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_160_intermediate_data_rlc c h_fixed (gate_160_of_meets_constraints h) (gate_132_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_161_intermediate_data_rlc c h_fixed (gate_161_of_meets_constraints h) (gate_133_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_162_intermediate_data_rlc c h_fixed (gate_162_of_meets_constraints h) (gate_134_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_163_intermediate_data_rlc c h_fixed (gate_163_of_meets_constraints h) (gate_135_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    exact Gates.LengthAndDataRlc.gate_164_intermediate_data_rlc c h_fixed (gate_164_of_meets_constraints h) (gate_136_of_meets_constraints h) (by omega) round h_round.2 h_round.1

  def length_equality_check_of_meets_constraints (h: meets_constraints c):
    ∀ round, length_equality_check  c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [length_equality_check]
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    have h_gate := Gates.LengthAndDataRlc.gate_165_length_equality_check c h_fixed (gate_165_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    simp_all [keccak_constants]

  def data_rlc_equality_check_of_meets_constraints (h: meets_constraints c):
    ∀ round, data_rlc_equality_check c round
  := by
    intro round
    obtain ⟨round, h_round⟩ := round
    replace h_round := Finset.mem_Icc.mp h_round
    simp [data_rlc_equality_check]
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    have h_gate := Gates.LengthAndDataRlc.gate_166_length_equality_check c h_fixed (gate_166_of_meets_constraints h) (by omega) round h_round.2 h_round.1
    simp_all [keccak_constants]

end Keccak.Proofs

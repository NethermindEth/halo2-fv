import Examples.Scroll.Keccak.Gates.HashRlcCheck
import Examples.Scroll.Keccak.Gates.Split
import Examples.Scroll.Keccak.Gates.SqueezeVerifyPacked.All
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Proofs

  lemma squeeze_from_parts_of_meets_constraints (h: meets_constraints c):
    ∀ round: Finset.Icc 1 24,
      (squeeze_from_parts c round).2
    := by
      intro round
      simp [squeeze_from_parts, Split.expr]
      obtain ⟨round, h_round⟩ := round
      replace h_round := Finset.mem_Icc.mp h_round
      have h_fixed := fixed_of_meets_constraints h
      have h_n := n_range_of_meets_constraints h
      dsimp
      convert Gates.Split.gate_77_split c h_fixed (gate_77_of_meets_constraints h) (by omega) (round-1) (by omega) <;> omega

  lemma squeeze_bytes_of_meets_constraints (h: meets_constraints c):
    ∀ round: Finset.Icc 1 24,
      (squeeze_bytes c round).2
    := by
      intro round
      simp [squeeze_bytes, Transform.split_expr]
      split_ands
      . have := squeeze_from_parts_of_meets_constraints h round
        simp_all [squeeze_from_parts, Split.expr]
      . simp [keccak_constants]
      . intro num_bits_in cell_in num_bits_out cell_out h_mem
        have h_fixed := fixed_of_meets_constraints h
        have h_lookup := Lookups.PackTable.lookup_86_pack_table c (lookup_86_of_meets_constraints h) h_fixed
        have h_goal: ∀ row < c.usable_rows,
          ∃ lookup_row, Lookups.PackTable.transform_table _ lookup_row = (c.get_advice 146 row, c.get_advice 147 row)
        := by
          intro row h_row
          specialize h_lookup row h_row
          obtain ⟨x, h_x, h_in, h_out⟩ := h_lookup
          use x
          simp [Lookups.PackTable.transform_table]
          rw [if_pos h_x, h_in, h_out]
        simp [squeeze_from_parts, Split.expr, Split.expr_res, word_parts_known, List.enum, cell_manager_to_col_row, cell_manager_column] at h_mem
        obtain ⟨round, h_round⟩ := round
        replace h_round := Finset.mem_Icc.mp h_round
        have h_usable_rows := usable_rows_range_of_meets_constraints h
        have h_n := n_range_of_meets_constraints h
        rcases h_mem with
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩ |
          ⟨⟨_, h_cell_in⟩, _, h_cell_out⟩
        all_goals {
          subst h_cell_in h_cell_out
          apply h_goal
          simp [cell_manager_row]
          rewrite [Nat.mod_eq_of_lt] <;> omega
        }

  lemma squeeze_verify_packed_of_meets_constraints (h: meets_constraints c):
    ∀ idx, squeeze_verify_packed c 25 idx
  := by
    have h_fixed := fixed_of_meets_constraints h
    have h_n := n_range_of_meets_constraints h
    unfold squeeze_verify_packed
    intro idx
    fin_cases idx
    . have h_gate := Gates.SqueezeVerifyPacked.gate_120_squeeze_verify_packed c h_fixed (gate_120_of_meets_constraints h) (by omega)
      simp_all [keccak_constants]
    . have h_gate := Gates.SqueezeVerifyPacked.gate_121_squeeze_verify_packed c h_fixed (gate_121_of_meets_constraints h) (by omega)
      simp_all [keccak_constants]
    . have h_gate := Gates.SqueezeVerifyPacked.gate_122_squeeze_verify_packed c h_fixed (gate_122_of_meets_constraints h) (by omega)
      simp_all [keccak_constants]
    . have h_gate := Gates.SqueezeVerifyPacked.gate_123_squeeze_verify_packed c h_fixed (gate_123_of_meets_constraints h) (by omega)
      simp_all [keccak_constants]

  lemma hash_rlc_check_of_meets_constraints (h: meets_constraints c):
    hash_rlc_check c 25
  := by
    simp [hash_rlc_check, keccak_constants, squeeze_rlc]
    have h_n := n_range_of_meets_constraints h
    exact Gates.HashRlcCheck.gate_124_hash_rlc_check
      c
      (fixed_of_meets_constraints h)
      (gate_124_of_meets_constraints h)
      (by omega)
end Keccak.Proofs

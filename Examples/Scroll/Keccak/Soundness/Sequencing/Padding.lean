import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.ProgramProofs.LengthAndDataRlc
import Examples.Scroll.Keccak.ProgramProofs.Padding

namespace Keccak.Soundness

  def padding (c: ValidCircuit P P_Prime) (n: ℕ): ℕ := (is_paddings c (n/8+1) (n%8)).val

  def padding_sum (c: ValidCircuit P P_Prime) (n: ℕ): ℕ :=
    match n with
      | 0 => padding c 0
      | (n+1) => padding c (n+1) + padding_sum c n

  lemma length_136 {c: ValidCircuit P P_Prime} (h: ∀ round: Finset.Icc 1 17, ∀ idx, is_paddings c round idx = 0) (h_meets_constraints: meets_constraints c) (h_P: P > 136):
    (length c (get_num_rows_per_round*17)).val = 136
  := by
    have h_update_length := Proofs.update_length_of_meets_constraints h_meets_constraints
    unfold update_length at h_update_length
    have h_fixed := fixed_of_meets_constraints h_meets_constraints
    simp [h] at h_update_length
    have h_1 := h_update_length 1
    simp [start_new_hash, ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1] at h_1
    have h_2 := h_update_length 2
    simp [start_new_hash, ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1, keccak_constants] at h_2

  lemma padding_end_one {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_length: (length c (get_num_rows_per_round*25)).val < 136) (h_P: P ≥ 136):
    is_paddings c 17 (-1) = 1
  := by
    have h_is_padding_boolean := Proofs.is_padding_boolean_of_meets_constraints h_meets_constraints
    unfold is_padding_boolean at h_is_padding_boolean
    have h_padding_step_boolean := Proofs.padding_step_boolean_of_meets_constraints h_meets_constraints
    unfold padding_step_boolean is_first_padding at h_padding_step_boolean
    have h_last_is_padding_on_absorb_rows := Proofs.last_is_padding_zero_on_absorb_rows_of_meets_constraints h_meets_constraints
    unfold last_is_padding_zero_on_absorb_rows at h_last_is_padding_on_absorb_rows
    have : Fact (1 < P) := by constructor; omega
    have h_le_one (x: ZMod P) (h: x = 0 ∨ x = 1): x.val ≤ 1 := by
      cases h
      . simp_all
      . simp_all [ZMod.val_one]
    have h_padding_sum_step (n: ℕ) (h: n+1 < 200): padding_sum c (n+1) - padding_sum c n ≤ 1 := by
      rewrite [padding_sum.eq_def]
      simp
      unfold padding
      apply (h_le_one _ (h_is_padding_boolean _ _ _))
      omega
    done

end Keccak.Soundness

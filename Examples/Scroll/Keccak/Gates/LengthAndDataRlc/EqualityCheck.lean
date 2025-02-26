import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Gates.Padding.IsPaddingBoolean
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Advice
import Examples.Scroll.Keccak.Spec.InputBytes
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.LengthAndDataRlc
  lemma gate_165_length_equality_check (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_165 c) (h_n: 288 < c.n):
    ∀ round ≤ 25, round > 17 → (
      length c (12*round) = length c (12*(round-1))
    ) := by
      unfold gate_165 at hgate
      intro round hround hround_lower
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, Selectors.fixed_1_q_first, Selectors.fixed_5_q_padding, to_named_advice] at hgate
      replace hgate := hgate (12*round)
      rewrite [Selectors.q_enable_at_round_start c hround] at hgate
      have hround': round ≠ 0 := by linarith
      have hround'': 12*round > 204 := by linarith
      have hround''': 12*round ≤ 311 := by linarith
      simp [Selectors.q_first, hround', hround'''] at hgate
      simp [Selectors.q_padding_late_rows, hround'', hround'''] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_involutive] at hgate
      rewrite [hgate]
      have h_n': 12 < c.n := by linarith
      have h_n'': 12 * round - 12 < c.n := lt_of_le_of_lt (
        by simp [Nat.mul_le_mul_left 12 hround]
      ) h_n
      rw [Nat.sub_add_comm, Nat.add_mod_right, Nat.mul_sub, Nat.mod_eq_of_lt h_n', Nat.mod_eq_of_lt h_n'', mul_one]
      exact le_trans (Nat.mod_le 12 c.n) (by linarith)

  lemma gate_166_length_equality_check (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_166 c) (h_n: 288 < c.n):
    ∀ round ≤ 25, round > 17 → (
      data_rlc c (12*round) = data_rlc c (12*(round-1))
    ) := by
      unfold gate_166 at hgate
      intro round hround hround_lower
      simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, Selectors.fixed_1_q_first, Selectors.fixed_5_q_padding, to_named_advice] at hgate
      replace hgate := hgate (12*round)
      rewrite [Selectors.q_enable_at_round_start c hround] at hgate
      have hround': round ≠ 0 := by linarith
      have hround'': 12*round > 204 := by linarith
      have hround''': 12*round ≤ 311 := by linarith
      simp [Selectors.q_first, hround', hround'''] at hgate
      simp [Selectors.q_padding_late_rows, hround'', hround'''] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_involutive] at hgate
      rewrite [hgate]
      have h_n': 12 < c.n := by linarith
      have h_n'': 12 * round - 12 < c.n := lt_of_le_of_lt (
        by simp [Nat.mul_le_mul_left 12 hround]
      ) h_n
      rw [Nat.sub_add_comm, Nat.add_mod_right, Nat.mul_sub, Nat.mod_eq_of_lt h_n', Nat.mod_eq_of_lt h_n'', mul_one]
      exact le_trans (Nat.mod_le 12 c.n) (by linarith)

import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.LengthAndDataRlc
  lemma gate_155_update_length (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_155 c) (h_is_final_first: is_final_disabled_on_first_row c) (h_is_final_boolean: boolean_is_final c) (h_n: 204 < c.n):
    ∀ round ≤ 17, round > 0 → (
      ((round = 1 ∨ is_final c (12*(round-1)) = 1) ∧ (
        length c (12*round) =
          (1 - is_paddings c round 0) +
          (1 - is_paddings c round 1) +
          (1 - is_paddings c round 2) +
          (1 - is_paddings c round 3) +
          (1 - is_paddings c round 4) +
          (1 - is_paddings c round 5) +
          (1 - is_paddings c round 6) +
          (1 - is_paddings c round 7)
      )) ∨ (
        (round ≠ 1 ∧ is_final c (12*(round-1)) = 0) ∧ (
          length c (12*round) =
            length c (12*(round-1)) +
            (1 - is_paddings c round 0) +
            (1 - is_paddings c round 1) +
            (1 - is_paddings c round 2) +
            (1 - is_paddings c round 3) +
            (1 - is_paddings c round 4) +
            (1 - is_paddings c round 5) +
            (1 - is_paddings c round 6) +
            (1 - is_paddings c round 7)
        )
      )
    )
  := by
    intro round hround hround_lower
    unfold gate_155 at hgate
    replace hgate := hgate (12*round)
    simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_5_q_padding, Selectors.q_padding_at_round_start, hround, hround_lower] at hgate
    replace hgate := eq_neg_of_add_eq_zero_left hgate
    simp at hgate
    have h_n': 12 < c.n := lt_trans (by trivial) h_n
    if hround1: round=1 then {
      simp_all
      rewrite [Nat.sub_add_comm (Nat.mod_le 12 c.n), Nat.mod_eq_of_lt (h_n')] at hgate
      norm_num at hgate
      unfold length
      rewrite [hgate]
      unfold is_final_disabled_on_first_row is_final at h_is_final_first
      simp [h_is_final_first, fixed_func, fixed_func_col_1, sub_eq_add_neg, is_paddings, cell_manager_to_raw, Nat.mod_eq_of_lt h_n']
    } else {
      simp_all
      if h_is_final: is_final c (12*(round-1)) = 0 then {
        right
        simp [h_is_final, length]
        rewrite [hgate]
        simp [sub_eq_add_neg, is_paddings, cell_manager_to_raw, fixed_func, fixed_func_col_1]
        rewrite [Nat.mod_eq_of_lt h_n']
        have h_first: (12*round + c.n - 12 ) % c.n ≠ 0 := by
          rewrite [Nat.sub_add_comm]
          . rewrite [Nat.add_mod_right, Nat.mod_eq_of_lt]
            . if h_contr: 12 * round - 12 = 0 then {
                rewrite [Nat.sub_eq_zero_iff_le] at h_contr
                exfalso
                match round with
                  | 0 => contradiction
                  | 1 => contradiction
                  | x+2 => contradiction
              } else {
                assumption
              }
            . exact lt_trans (
                lt_of_lt_of_le (@Nat.sub_lt (12*round) 12 (by omega) (by trivial)) (by omega)
              ) h_n
          . match round with
              | 0 => contradiction
              | x+1 => rewrite [mul_add, mul_one]; exact le_add_self
        simp [h_first]
        have h: 1 ≤ (12*round+c.n-12) % c.n := by
          rewrite [Nat.sub_add_comm]
          . rewrite [Nat.add_mod_right, Nat.mod_eq_of_lt]
            . have h: 2 ≤ round := by match round with
                | 0 | 1 => contradiction
                | x+2 => exact Nat.le_add_left 2 x
              rewrite [Nat.le_sub_iff_add_le] <;> omega
            . exact lt_trans (
                lt_of_lt_of_le (@Nat.sub_lt (12*round) 12 (by omega) (by trivial)) (by omega)
              ) h_n
          . match round with
              | 0 => contradiction
              | x+1 => rewrite [mul_add, mul_one]; exact le_add_self
        simp [h]
        have h: (12*round + c.n - 12) % c.n ≤ 311 := by
          rewrite [Nat.sub_add_comm]
          . rewrite [Nat.add_mod_right, Nat.mod_eq_of_lt]
            . rewrite [Nat.sub_le_iff_le_add] ; omega
            . exact lt_trans (
                lt_of_lt_of_le (@Nat.sub_lt (12*round) 12 (by omega) (by trivial)) (by omega)
              ) h_n
          . match round with
            | 0 => contradiction
            | x+1 => rewrite [mul_add, mul_one]; exact le_add_self
        simp [h]
        simp [is_final, Nat.mul_sub] at h_is_final
        rewrite [Nat.sub_add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt, h_is_final]
        . simp [Nat.mul_sub, add_assoc, add_right_inj]
          rw [Nat.mod_eq_of_lt] ; omega
        . exact lt_trans (
            lt_of_lt_of_le (@Nat.sub_lt (12*round) 12 (by omega) (by trivial)) (by omega)
          ) h_n
        . omega
      } else {
        left
        unfold boolean_is_final is_final at h_is_final_boolean
        have h: round-1 ≤ 25 := le_trans (Nat.sub_le round 1) (le_trans hround (by trivial))
        replace h_is_final_boolean := h_is_final_boolean (round-1) h
        simp_all [is_final]
        unfold length
        rewrite [hgate]
        simp [sub_eq_add_neg]
        rewrite [Nat.sub_add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt h_n', Nat.mod_eq_of_lt]
        . rewrite [Nat.mul_sub, mul_one] at h_is_final_boolean
          rewrite [h_is_final_boolean]
          simp [fixed_func, fixed_func_col_1]
          have h: 12 * round - 12 ≠ 0 := by
            rewrite [ne_eq, Nat.sub_eq_zero_iff_le, not_le]
            match round with
              | 0 => contradiction
              | 1 => contradiction
              | x+2 => omega
          simp [h]
          have h: 1 ≤ 12 * round - 12 := by match round with
            | 0 | 1 => contradiction
            | x+2 => simp [mul_add]
          simp [h]
          have h: 12 * round ≤ 323 := by omega
          simp [h, is_paddings, cell_manager_to_raw]
          rw [Nat.mod_eq_of_lt]
          exact lt_of_le_of_lt (
            Nat.mul_le_mul (le_of_eq (by trivial)) hround
          ) h_n
        . exact lt_trans (
            lt_of_lt_of_le (@Nat.sub_lt (12*round) 12 (by omega) (by trivial)) (by omega)
          ) h_n
        . rewrite [Nat.mod_eq_of_lt h_n']
          match round with
            | 0 | 1 => contradiction
            | x+2 => omega
      }
    }


end Keccak.Gates.LengthAndDataRlc

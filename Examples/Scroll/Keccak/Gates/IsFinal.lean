import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Selectors
import Examples.Scroll.Keccak.Spec.Advice
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Gates.IsFinal
  lemma gate_127_is_final_eq_last_is_padding (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_127 c) (h_n: 211 < c.n):
    is_final c 300 = last_is_padding_in_block c 25 7
  := by
    unfold gate_127 at hgate
    replace hgate := hgate 300
    have h_n': 89 < c.n := by linarith
    simp [ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1, fixed_func_col_3, h_n'] at hgate
    rewrite [Nat.sub_add_comm, Nat.mod_eq_of_lt h_n'] at hgate
    . simp [Nat.mod_eq_of_lt h_n, to_named_advice, to_cell_manager] at hgate
      replace hgate := eq_neg_of_add_eq_zero_left hgate
      rewrite [neg_involutive] at hgate
      rewrite [hgate]
      simp [last_is_padding_in_block, keccak_constants, is_paddings, cell_manager, ValidCircuit.get_advice_wrapped, Nat.mod_eq_of_lt h_n]
    . simp [Nat.mod_eq_of_lt h_n']

  lemma gate_128_is_final_only_when_q_enable (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_128 c) (h_n: 300 < c.n):
    ∀ row ≤ 300, 11 ≤ row → is_final c row = 1 → Selectors.q_enable c row = 1
  := by
    unfold gate_128 at hgate
    intro row hrow h_row_lower h_is_final
    replace hgate := hgate row
    simp [ValidCircuit.get_fixed, h_fixed, Selectors.fixed_0_q_enable, to_named_advice, h_is_final] at hgate
    have h1: 1 < c.n := lt_trans (by trivial) h_n
    have h2: 2 < c.n := lt_trans (by trivial) h_n
    have h3: 3 < c.n := lt_trans (by trivial) h_n
    have h4: 4 < c.n := lt_trans (by trivial) h_n
    have h5: 5 < c.n := lt_trans (by trivial) h_n
    have h6: 6 < c.n := lt_trans (by trivial) h_n
    have h7: 7 < c.n := lt_trans (by trivial) h_n
    have h8: 8 < c.n := lt_trans (by trivial) h_n
    have h9: 9 < c.n := lt_trans (by trivial) h_n
    have h10: 10 < c.n := lt_trans (by trivial) h_n
    have h11: 11 < c.n := lt_trans (by trivial) h_n
    simp_all [Nat.mod_eq_of_lt]
    rewrite [
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower),
      Nat.sub_add_comm (le_trans (by trivial) h_row_lower)
    ] at hgate
    simp only [Nat.add_mod_right] at hgate
    have h_mod {a: ℕ}: a ≤ 299 → a % c.n = a := by intro h; apply Nat.mod_eq_of_lt; linarith
    have h_sub {x: ℕ}: (row - x) % c.n ≤ 311 := by
      rewrite [Nat.mod_eq_of_lt]
      apply Nat.sub_le_of_le_add
      linarith
      exact lt_of_le_of_lt (le_trans (Nat.sub_le row x) hrow) h_n
    have h_sub' {x: ℕ}: (row - x) % c.n = row -x := by
      rw [Nat.mod_eq_of_lt]
      have h := Nat.sub_le_add_right_sub row x x
      rewrite [Nat.add_sub_cancel] at h
      exact lt_of_le_of_lt (le_trans h hrow) h_n
    simp [h_sub'] at hgate
    clear h_fixed h_is_final h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h_mod h_sub h_sub'
    sorry

end Keccak.Gates.IsFinal

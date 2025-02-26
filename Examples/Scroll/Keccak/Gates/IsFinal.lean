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

  private lemma aux (c: ValidCircuit P P_Prime) (row x: ℕ): row + x ≤ 311 → 0 < x → x < 11 → 12 ∣ row → Selectors.q_enable c (row + x) = 0 := by
    intro hrow hx_low hx hdvd
    apply Selectors.q_enable_not_dvd
    exact hrow
    rewrite [Nat.dvd_iff_mod_eq_zero] at hdvd ⊢
    rewrite [Nat.add_mod, hdvd, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
    linarith
    exact lt_trans hx (by trivial)


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
    generalize hrow': row - 11 = row'
    replace hgate : Selectors.q_enable c (row' + 10) +
      Selectors.q_enable c (row' + 9) +
      Selectors.q_enable c (row' + 8) +
      Selectors.q_enable c (row' + 7) +
      Selectors.q_enable c (row' + 6) +
      Selectors.q_enable c (row' + 5) +
      Selectors.q_enable c (row' + 4) +
      Selectors.q_enable c (row' + 3) +
      Selectors.q_enable c (row' + 2) +
      Selectors.q_enable c (row' + 1) +
      Selectors.q_enable c row' = 0 := by
        rewrite [←hgate]
        simp [←hrow']
        congr
        exact @Nat.sub_add_sub_cancel row 11 1 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 2 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 3 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 4 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 5 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 6 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 7 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 8 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 9 h_row_lower (by trivial)
        exact @Nat.sub_add_sub_cancel row 11 10 h_row_lower (by trivial)

    have hrow'_range: row' ≤ 289 := by
      rewrite [←hrow', Nat.sub_le_iff_le_add]
      exact hrow

    if h0: 12 ∣ row' then {
      rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h0] at hgate
      rewrite [aux c row' 1 (@Nat.add_le_add _ _ 1 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 2 (@Nat.add_le_add _ _ 2 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 3 (@Nat.add_le_add _ _ 3 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 4 (@Nat.add_le_add _ _ 4 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 5 (@Nat.add_le_add _ _ 5 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 6 (@Nat.add_le_add _ _ 6 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 7 (@Nat.add_le_add _ _ 7 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 8 (@Nat.add_le_add _ _ 8 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 9 (@Nat.add_le_add _ _ 9 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0, add_zero] at hgate
      rewrite [aux c row' 10 (@Nat.add_le_add _ _ 10 22 hrow'_range (by trivial)) (by trivial) (by trivial) h0] at hgate
      simp [zmod_p_one_neq_zero P_Prime] at hgate
    } else {
      rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h0, add_zero] at hgate
      if h1: 12 ∣ row' + 1 then {
        rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h1] at hgate
        rewrite [aux c (row' + 1) 1 (@Nat.add_le_add (row'+1) 290 1 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 2 (@Nat.add_le_add (row'+1) 290 2 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 3 (@Nat.add_le_add (row'+1) 290 3 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 4 (@Nat.add_le_add (row'+1) 290 4 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 5 (@Nat.add_le_add (row'+1) 290 5 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 6 (@Nat.add_le_add (row'+1) 290 6 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 7 (@Nat.add_le_add (row'+1) 290 7 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 8 (@Nat.add_le_add (row'+1) 290 8 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        rewrite [aux c (row' + 1) 9 (@Nat.add_le_add (row'+1) 290 9 21 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h1] at hgate
        simp [zmod_p_one_neq_zero P_Prime] at hgate
      } else {
        rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h1, add_zero] at hgate
        if h2: 12 ∣ row' + 2 then {
          rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h2] at hgate
          rewrite [aux c (row' + 2) 1 (@Nat.add_le_add (row'+2) 291 1 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 2 (@Nat.add_le_add (row'+2) 291 2 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 3 (@Nat.add_le_add (row'+2) 291 3 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 4 (@Nat.add_le_add (row'+2) 291 4 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 5 (@Nat.add_le_add (row'+2) 291 5 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 6 (@Nat.add_le_add (row'+2) 291 6 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 7 (@Nat.add_le_add (row'+2) 291 7 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          rewrite [aux c (row' + 2) 8 (@Nat.add_le_add (row'+2) 291 8 20 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h2] at hgate
          simp [zmod_p_one_neq_zero P_Prime] at hgate
        } else {
          rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h2, add_zero] at hgate
          if h3: 12 ∣ row' + 3 then {
            rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h3] at hgate
            rewrite [aux c (row' + 3) 1 (@Nat.add_le_add (row'+3) 292 1 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            rewrite [aux c (row' + 3) 2 (@Nat.add_le_add (row'+3) 292 2 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            rewrite [aux c (row' + 3) 3 (@Nat.add_le_add (row'+3) 292 3 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            rewrite [aux c (row' + 3) 4 (@Nat.add_le_add (row'+3) 292 4 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            rewrite [aux c (row' + 3) 5 (@Nat.add_le_add (row'+3) 292 5 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            rewrite [aux c (row' + 3) 6 (@Nat.add_le_add (row'+3) 292 6 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            rewrite [aux c (row' + 3) 7 (@Nat.add_le_add (row'+3) 292 7 19 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h3] at hgate
            simp [zmod_p_one_neq_zero P_Prime] at hgate
          } else {
            rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h3, add_zero] at hgate
            if h4: 12 ∣ row' + 4 then {
              rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h4] at hgate
              rewrite [aux c (row' + 4) 1 (@Nat.add_le_add (row'+4) 293 1 18 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h4] at hgate
              rewrite [aux c (row' + 4) 2 (@Nat.add_le_add (row'+4) 293 2 18 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h4] at hgate
              rewrite [aux c (row' + 4) 3 (@Nat.add_le_add (row'+4) 293 3 18 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h4] at hgate
              rewrite [aux c (row' + 4) 4 (@Nat.add_le_add (row'+4) 293 4 18 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h4] at hgate
              rewrite [aux c (row' + 4) 5 (@Nat.add_le_add (row'+4) 293 5 18 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h4] at hgate
              rewrite [aux c (row' + 4) 6 (@Nat.add_le_add (row'+4) 293 6 18 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h4] at hgate
              simp [zmod_p_one_neq_zero P_Prime] at hgate
            } else {
              rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h4, add_zero] at hgate
              if h5: 12 ∣ row' + 5 then {
                rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h5] at hgate
                rewrite [aux c (row' + 5) 1 (@Nat.add_le_add (row'+5) 294 1 17 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h5] at hgate
                rewrite [aux c (row' + 5) 2 (@Nat.add_le_add (row'+5) 294 2 17 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h5] at hgate
                rewrite [aux c (row' + 5) 3 (@Nat.add_le_add (row'+5) 294 3 17 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h5] at hgate
                rewrite [aux c (row' + 5) 4 (@Nat.add_le_add (row'+5) 294 4 17 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h5] at hgate
                rewrite [aux c (row' + 5) 5 (@Nat.add_le_add (row'+5) 294 5 17 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h5] at hgate
                simp [zmod_p_one_neq_zero P_Prime] at hgate
              } else {
                rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h5, add_zero] at hgate
                if h6: 12 ∣ row' + 6 then {
                  rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h6] at hgate
                  rewrite [aux c (row' + 6) 1 (@Nat.add_le_add (row'+6) 295 1 16 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h6] at hgate
                  rewrite [aux c (row' + 6) 2 (@Nat.add_le_add (row'+6) 295 2 16 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h6] at hgate
                  rewrite [aux c (row' + 6) 3 (@Nat.add_le_add (row'+6) 295 3 16 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h6] at hgate
                  rewrite [aux c (row' + 6) 4 (@Nat.add_le_add (row'+6) 295 4 16 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h6] at hgate
                  simp [zmod_p_one_neq_zero P_Prime] at hgate
                } else {
                  rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h6, add_zero] at hgate
                  if h7: 12 ∣ row' + 7 then {
                    rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h7] at hgate
                    rewrite [aux c (row' + 7) 1 (@Nat.add_le_add (row'+7) 296 1 15 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h7] at hgate
                    rewrite [aux c (row' + 7) 2 (@Nat.add_le_add (row'+7) 296 2 15 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h7] at hgate
                    rewrite [aux c (row' + 7) 3 (@Nat.add_le_add (row'+7) 296 3 15 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h7] at hgate
                    simp [zmod_p_one_neq_zero P_Prime] at hgate
                  } else {
                    rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h7, add_zero] at hgate
                    if h8: 12 ∣ row' + 8 then {
                      rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h8] at hgate
                      rewrite [aux c (row' + 8) 1 (@Nat.add_le_add (row'+8) 297 1 14 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h8] at hgate
                      rewrite [aux c (row' + 8) 2 (@Nat.add_le_add (row'+8) 297 2 14 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h8] at hgate
                      simp [zmod_p_one_neq_zero P_Prime] at hgate
                    } else {
                      rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h8, add_zero] at hgate
                      if h9: 12 ∣ row' + 9 then {
                        rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h9] at hgate
                        rewrite [aux c (row' + 9) 1 (@Nat.add_le_add (row'+9) 298 1 13 (Nat.add_le_add hrow'_range (by trivial)) (by trivial)) (by trivial) (by trivial) h9] at hgate
                        simp [zmod_p_one_neq_zero P_Prime] at hgate
                      } else {
                        rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h9, add_zero] at hgate
                        if h10: 12 ∣ row' + 10 then {
                          rewrite [Selectors.q_enable_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h10] at hgate
                          simp [zmod_p_one_neq_zero P_Prime] at hgate
                        } else {
                          rewrite [Selectors.q_enable_not_dvd c (by subst hrow'; simp; exact le_trans hrow (by trivial)) h10] at hgate
                          apply Selectors.q_enable_dvd
                          . exact le_trans hrow (by trivial)
                          . have h: row = row' + 11 := by
                              rw [←hrow', Nat.sub_add_cancel h_row_lower]
                            rewrite [h]
                            rewrite [Nat.dvd_iff_mod_eq_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
                            rewrite [Nat.add_mod] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ⊢
                            rewrite [@Nat.mod_eq_of_lt 1 12 (by trivial)] at h1
                            rewrite [@Nat.mod_eq_of_lt 2 12 (by trivial)] at h2
                            rewrite [@Nat.mod_eq_of_lt 3 12 (by trivial)] at h3
                            rewrite [@Nat.mod_eq_of_lt 4 12 (by trivial)] at h4
                            rewrite [@Nat.mod_eq_of_lt 5 12 (by trivial)] at h5
                            rewrite [@Nat.mod_eq_of_lt 6 12 (by trivial)] at h6
                            rewrite [@Nat.mod_eq_of_lt 7 12 (by trivial)] at h7
                            rewrite [@Nat.mod_eq_of_lt 8 12 (by trivial)] at h8
                            rewrite [@Nat.mod_eq_of_lt 9 12 (by trivial)] at h9
                            rewrite [@Nat.mod_eq_of_lt 10 12 (by trivial)] at h10
                            rewrite [@Nat.mod_eq_of_lt 11 12 (by trivial)]
                            match h': (row' % 12) with
                              | 0 => rewrite [h'] at h0; contradiction
                              | 1 => simp
                              | 2 => rewrite [h'] at h10; contradiction
                              | 3 => rewrite [h'] at h9; contradiction
                              | 4 => rewrite [h'] at h8; contradiction
                              | 5 => rewrite [h'] at h7; contradiction
                              | 6 => rewrite [h'] at h6; contradiction
                              | 7 => rewrite [h'] at h5; contradiction
                              | 8 => rewrite [h'] at h4; contradiction
                              | 9 => rewrite [h'] at h3; contradiction
                              | 10 => rewrite [h'] at h2; contradiction
                              | 11 => rewrite [h'] at h1; contradiction
                              | x+12 =>
                                exfalso
                                have _ := @Nat.mod_lt row' 12 (by trivial)
                                linarith
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }


end Keccak.Gates.IsFinal

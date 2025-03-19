import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak.FinVals
  @[fin_vals] lemma fin_5_val_4: @Fin.val 5 4 = 4 := rfl

  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_0: @Fin.val rho_by_pi_num_word_parts 0 = 0 := rfl
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_1: @Fin.val rho_by_pi_num_word_parts 1 = 1 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_2: @Fin.val rho_by_pi_num_word_parts 2 = 2 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_3: @Fin.val rho_by_pi_num_word_parts 3 = 3 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_4: @Fin.val rho_by_pi_num_word_parts 4 = 4 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_5: @Fin.val rho_by_pi_num_word_parts 5 = 5 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_6: @Fin.val rho_by_pi_num_word_parts 6 = 6 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_7: @Fin.val rho_by_pi_num_word_parts 7 = 7 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_8: @Fin.val rho_by_pi_num_word_parts 8 = 8 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_9: @Fin.val rho_by_pi_num_word_parts 9 = 9 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_10: @Fin.val rho_by_pi_num_word_parts 10 = 10 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_11: @Fin.val rho_by_pi_num_word_parts 11 = 11 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_12: @Fin.val rho_by_pi_num_word_parts 12 = 12 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_13: @Fin.val rho_by_pi_num_word_parts 13 = 13 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_14: @Fin.val rho_by_pi_num_word_parts 14 = 14 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
  @[fin_vals] lemma fin_rho_by_pi_word_parts_val_15: @Fin.val rho_by_pi_num_word_parts 15 = 15 := by rewrite [Fin.coe_ofNat_eq_mod]; simp [keccak_constants]
end Keccak.FinVals

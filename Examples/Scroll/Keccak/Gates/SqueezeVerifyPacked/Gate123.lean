import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Selectors

namespace Keccak

  namespace Gates

    namespace SqueezeVerifyPacked

      -- TODO prove in reverse direction
      lemma gate_123_squeeze_verify_packed (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_123 c) (h_n: 303 < c.n):
        start_new_hash c 300 → hash_words c 25 3 = squeeze_from c 21
      := by
        unfold gate_123 at hgate
        intro h_start
        simp only [hash_words, s]
        rewrite [Fin.coe_ofNat_eq_mod]
        simp
        replace hgate := hgate 300
        simp [ValidCircuit.get_fixed, h_fixed, Selectors.q_round_last_one, one_mul] at hgate
        simp [fixed_func, fixed_func_col_1] at hgate
        simp [start_new_hash, ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1, zmod_not_zero_eq_one, P_Prime, is_final] at h_start
        simp [h_start] at hgate
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        unfold squeeze_from cell_manager ValidCircuit.get_advice_wrapped
        norm_num
        have h_n': 252 < c.n := by omega
        have h_n'': 48 < c.n := by omega
        simp_all [Nat.mod_eq_of_lt, Nat.sub_add_comm]

    end SqueezeVerifyPacked

  end Gates

end Keccak

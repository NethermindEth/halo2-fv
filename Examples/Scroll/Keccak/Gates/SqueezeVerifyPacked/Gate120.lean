import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Selectors

namespace Keccak

  namespace Gates

    namespace SqueezeVerifyPacked

      -- TODO structure proof in reverse direction
      lemma gate_120_squeeze_verify_packed (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_120 c) (h_n: 300 < c.n):
        start_new_hash c 300 → hash_words c 25 0 = squeeze_from c 24
      := by
        unfold gate_120 at hgate
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
        have h_n': 288 < c.n := by omega
        simp [Nat.mod_eq_of_lt, h_n, h_n']
        rewrite [hgate]
        congr
        have h_n'': 12 < c.n := by omega
        simp [Nat.mod_eq_of_lt, h_n', h_n'', Nat.sub_add_comm]

    end SqueezeVerifyPacked

  end Gates

end Keccak

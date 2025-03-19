import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Spec.Advice
import Examples.Scroll.Keccak.Spec.ComposeRlc
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  namespace Gates
    namespace HashRlcCheck

      lemma gate_124_hash_rlc_check (c: ValidCircuit P P_Prime) (h_fixed: c.1.Fixed = fixed_func c) (hgate: gate_124 c) (h_n: 263 < c.n) :
        start_new_hash c 300 → ComposeRlc.expr (hash_bytes_le c 25) (c.get_challenge 0 0) = hash_rlc c 300
      := by
        unfold gate_124 at hgate
        intro h_start
        simp [start_new_hash, ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1, zmod_not_zero_eq_one, P_Prime, is_final] at h_start
        replace hgate := hgate 300
        simp [ValidCircuit.get_fixed, h_fixed, Selectors.q_round_last_one, one_mul, h_start] at hgate
        simp [fixed_func, fixed_func_col_1] at hgate
        replace hgate := eq_neg_of_add_eq_zero_left hgate
        rewrite [neg_involutive] at hgate
        simp [to_named_advice] at hgate
        symm at hgate
        rewrite [hgate]
        clear hgate
        simp [hash_bytes_le, hash_bytes, squeeze_bytes, squeeze_from_parts, Transform.split_expr, Split.expr_res, word_parts_known, cell_manager_to_raw]
        have h (k: ℕ): k < 49 → k % c.n = k := by
          intro hk
          rw [Nat.mod_eq_of_lt]
          omega
        simp [h]
        simp [Nat.sub_add_comm]
        unfold ComposeRlc.expr
        rewrite [List.foldl_cons]
        simp

    end HashRlcCheck
  end Gates
end Keccak

import Examples.Scroll.Keccak.CellManager
import Examples.Scroll.Keccak.Spec.ComposeRlc
import Examples.Scroll.Keccak.Spec.HashRlc
import Examples.Scroll.Keccak.Spec.Program

-- def expr (l: List (ZMod P)) (r k: ZMod P) (hk: k = r ^ (l.length)) :=
--   (l.enum.map (λ (idx, val) => val * (r ^ idx))).sum
-- lemma base (val val' r: ZMod P): val + val' * r = expr [val, val'] r (r*r) (by simp [List.length, pow_two]) := by
--   simp [expr, List.map]
-- lemma cons: expr l r (k*r) hk + val * (k * r) = expr (l ++ [val]) r (k*r*r) (by simp [hk, pow_add]) := by
--   simp [expr]
--   rewrite [List.enum_append, List.map_append, List.sum_append]
--   congr
--   simp [hk]

-- lemma to_rlc: expr l r k hk = Keccak.ComposeRlc.expr l r := by
--   unfold Keccak.ComposeRlc.expr expr
--   simp [List.sum_eq_foldr, ←List.foldl_eq_foldr]



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
        rewrite [to_hash_rlc] at hgate
        rewrite [←hgate]
        clear hgate
        simp only [hash_bytes_le, hash_bytes, cell_manager, List.reverse, List.reverseAux]
        norm_num
        simp only [ValidCircuit.get_advice_wrapped, Nat.reduceAdd]
        have h (k: ℕ): k < 49 → k % c.n = k := by
          intro hk
          rw [Nat.mod_eq_of_lt]
          linarith
        simp [h]
        simp [Nat.sub_add_comm]
        unfold ComposeRlc.expr
        rewrite [List.foldl_cons]
        simp

    end HashRlcCheck
  end Gates
end Keccak

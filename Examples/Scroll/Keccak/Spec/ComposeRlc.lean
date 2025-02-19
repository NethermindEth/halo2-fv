import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  namespace ComposeRlc
    lemma to_rlc_base (val r: ZMod P): val * k + val' * (k * r) = expr [val*k, val'*k] r := by simp [expr, mul_assoc]
    lemma to_rlc_cons: expr [val] r + val' * r = expr [val, val'] r := by simp [expr]
  end ComposeRlc
end Keccak

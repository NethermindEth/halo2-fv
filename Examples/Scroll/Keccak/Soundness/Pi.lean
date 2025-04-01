import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Theta
import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Soundness.Bc
import Examples.Scroll.Keccak.Soundness.Lookups
import Examples.Scroll.Keccak.Soundness.Util

namespace Keccak.Soundness

  lemma pi_size :
    (LeanCrypto.HashFunctions.π state).size ≥ 25
  := by
    unfold LeanCrypto.HashFunctions.π
    simp [Array.backpermute.eq_def, LeanCrypto.HashFunctions.piConstants.eq_def]

  def pi_get (data: Fin 5 → Fin 5 → T) (x y: Fin 5) : T := data y (3*x + y)

  lemma pi (state: LeanCrypto.HashFunctions.SHA3SR) (h_state: state.size ≥ 25):
    state_get (LeanCrypto.HashFunctions.π state) (pi_size) x y =
    pi_get (state_get state h_state) x y := by
    unfold LeanCrypto.HashFunctions.π LeanCrypto.HashFunctions.piConstants pi_get
    simp [Array.backpermute]
    fin_cases x <;> fin_cases y
    all_goals simp_all [state_get.eq_def, fin_vals, Fin.isValue]
    all_goals rewrite [Option.getD_eq_iff]; left
    all_goals aesop

  lemma os_parts_equiv_pi:
    os_parts c round y x =
    (pi_get (λ x y => s_parts' c round y x) x y).1
  := by
    unfold pi_get
    fin_cases x <;> fin_cases y
    all_goals simp [fin_vals, os_parts.eq_def]

end Keccak.Soundness

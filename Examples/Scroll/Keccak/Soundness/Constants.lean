import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Spec.FinVals

namespace Keccak.Soundness


  def UInt64_to_normalize_3_Nat (input: UInt64) :=
    List.range 64
    |>.map (λ x => (
      UInt64.ofNat 1 <<< UInt64.ofNat x,
      BitVec.ofNat 192 1 |>.shiftLeft (x*3))
    )
    |>.filter (λ ⟨x, _⟩ => x &&& input ≠ UInt64.ofNat 0)
    |>.foldr (λ ⟨_, val⟩ acc => val ||| acc) (BitVec.ofNat 192 0)
    |>.toNat


  lemma round_cst_eq_normalize_3_RoundConstants {c: ValidCircuit P P_Prime} (h: meets_constraints c) (h_p: 784637716923335095479473677910861822327077507941571493889 < P) (h_round: round < 312): .some ((round_cst c round).val) = (0 :: LeanCrypto.HashFunctions.RoundConstants.toList ++ [0])[round/get_num_rows_per_round]?.map UInt64_to_normalize_3_Nat := by
    simp [round_cst, fixed_of_meets_constraints h, ValidCircuit.get_fixed, fixed_func, LeanCrypto.HashFunctions.RoundConstants, keccak_constants]
    match h: round/12 with
      | 0 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_pos (by omega)]
        simp
        decide
      | 1 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_pos (by omega), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        decide
      | 2 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 3 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 4 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 5 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 6 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 7 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 8 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 9 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 10 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 11 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 12 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 13 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 14 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 15 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 16 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 17 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 18 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 19 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 20 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 21 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 22 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 23 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 24 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt]
        . decide
        . exact lt_of_le_of_lt (by trivial) h_p
      | 25 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_normalize_3_Nat, list_ops]
        decide
      | x+26 => exfalso; omega

  lemma rotationConstants_eq_rho_matrix : .some (RHO_MATRIX x y) = LeanCrypto.HashFunctions.rotationConstants[5*x.val+y.val]? := by
    fin_cases x <;> fin_cases y
    all_goals simp [RHO_MATRIX, LeanCrypto.HashFunctions.rotationConstants, fin_vals]


end Keccak.Soundness

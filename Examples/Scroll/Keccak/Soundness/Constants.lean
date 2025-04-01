import Mathlib.Data.ZMod.Basic

import LeanCrypto.Primitives.HashFunctions.Keccak256

import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Soundness.Util
import Examples.Scroll.Keccak.Spec.FinVals

namespace Keccak.Soundness

  lemma round_cst_eq_unpacked_RoundConstants {c: ValidCircuit P P_Prime} (h: meets_constraints c) (h_p: 784637716923335095479473677910861822327077507941571493889 < P) (h_row: row < 312):
    .some ((round_cst c row).val) =
    (0 :: LeanCrypto.HashFunctions.RoundConstants.toList ++ [0])[row/get_num_rows_per_round]?.map UInt64_to_unpacked_Nat
  := by
    simp [round_cst, fixed_of_meets_constraints h, ValidCircuit.get_fixed, fixed_func, LeanCrypto.HashFunctions.RoundConstants, keccak_constants]
    match h: row/12 with
      | 0 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_pos (by omega)]
        simp
        decide
      | 1 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_pos (by omega), ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        decide
      | 2 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 3 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 4 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 5 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 6 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 7 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 8 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 9 =>
        rewrite [fixed_func_col_7, if_pos (by omega), fixed_func_col_7_0_to_119, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 10 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 11 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 12 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 13 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 14 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 15 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 16 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 17 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 18 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 19 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_pos (by omega), fixed_func_col_7_120_to_239, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 20 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 21 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 22 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 23 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 24 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]; norm_num
        convert ZMod.val_natCast _
        rewrite [Nat.mod_eq_of_lt (lt_of_le_of_lt (by trivial) h_p)]
        decide
      | 25 =>
        rewrite [fixed_func_col_7, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        simp [UInt64_to_unpacked_Nat, list_ops]
        decide
      | x+26 => exfalso; omega

  lemma rotationConstants_eq_rho_matrix : .some (RHO_MATRIX y x) = LeanCrypto.HashFunctions.rotationConstants[5*y.val+x.val]? := by
    fin_cases y <;> fin_cases x
    all_goals simp [RHO_MATRIX, LeanCrypto.HashFunctions.rotationConstants, fin_vals]


end Keccak.Soundness

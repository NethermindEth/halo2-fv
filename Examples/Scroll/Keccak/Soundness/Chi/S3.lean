import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Soundness.Chi.ChiBase
import Examples.Scroll.Keccak.Soundness.Chi.LookupCols
import Examples.Scroll.Keccak.Soundness.Chi.SeparateDecode
import Examples.Scroll.Keccak.Soundness.Chi.State
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.NormalizeRho.All
import Examples.Scroll.Keccak.Soundness.RhoState
import Examples.Scroll.Keccak.Soundness.RhoRange.All
import Examples.Scroll.Keccak.Spec.Program
import Examples.Util

namespace Keccak.Soundness

  lemma chi_os'_3_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2690186458022863184501052609946142749758152333341729076955<P):
    (os' c round 3 0).val =
    Normalize.normalize_unpacked (
      rho_s_3_3 c round ^^^ (
        bit_invert (rho_s_4_4 c round) 64 &&&
        rho_s_0_0 c round
      )
    ) 64
  := by
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round' := Finset.mem_Icc.mp h_round
    have h_P': P ≥ 4096 := by omega
    simp [os', keccak_constants, list_ops, rho_pi_chi_cells, cell_manager_to_raw]
    have : 12 * round % c.n = 12 * round := by rw [Nat.mod_eq_of_lt (by omega)]
    have h_to_cell_manager: 12 * round + 11 < c.n := by omega
    have h_lookup_P: P ≥ 1756 := by omega
    have h_normalize_rho_0 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_73 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_1 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_74 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_2 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_70 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_3 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_78 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_4 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_79 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_5 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_75 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    try simp [fin_vals]
    rewrite [
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_0 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_1 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_2 0 (by trivial))),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 1 (by trivial)) (h_normalize_rho_1 1 (by trivial)) (h_normalize_rho_2 1 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 2 (by trivial)) (h_normalize_rho_1 2 (by trivial)) (h_normalize_rho_2 2 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 3 (by trivial)) (h_normalize_rho_1 3 (by trivial)) (h_normalize_rho_2 3 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 4 (by trivial)) (h_normalize_rho_1 4 (by trivial)) (h_normalize_rho_2 4 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 5 (by trivial)) (h_normalize_rho_1 5 (by trivial)) (h_normalize_rho_2 5 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 6 (by trivial)) (h_normalize_rho_1 6 (by trivial)) (h_normalize_rho_2 6 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 7 (by trivial)) (h_normalize_rho_1 7 (by trivial)) (h_normalize_rho_2 7 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 8 (by trivial)) (h_normalize_rho_1 8 (by trivial)) (h_normalize_rho_2 8 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 9 (by trivial)) (h_normalize_rho_1 9 (by trivial)) (h_normalize_rho_2 9 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 10 (by trivial)) (h_normalize_rho_1 10 (by trivial)) (h_normalize_rho_2 10 (by trivial)),
      chi_base_0_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 11 (by trivial)) (h_normalize_rho_1 11 (by trivial)) (h_normalize_rho_2 11 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_3 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_4 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_5 0 (by trivial))),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 1 (by trivial)) (h_normalize_rho_4 1 (by trivial)) (h_normalize_rho_5 1 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 2 (by trivial)) (h_normalize_rho_4 2 (by trivial)) (h_normalize_rho_5 2 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 3 (by trivial)) (h_normalize_rho_4 3 (by trivial)) (h_normalize_rho_5 3 (by trivial)),
    ]
    rewrite [
      lookup_zero_rot (h_normalize_rho_0 0 (by trivial)), lookup_zero_rot (h_normalize_rho_1 0 (by trivial)), lookup_zero_rot (h_normalize_rho_2 0 (by trivial)),
      (h_normalize_rho_0 1 (by trivial)), (h_normalize_rho_1 1 (by trivial)), (h_normalize_rho_2 1 (by trivial)),
      (h_normalize_rho_0 2 (by trivial)), (h_normalize_rho_1 2 (by trivial)), (h_normalize_rho_2 2 (by trivial)),
      (h_normalize_rho_0 3 (by trivial)), (h_normalize_rho_1 3 (by trivial)), (h_normalize_rho_2 3 (by trivial)),
      (h_normalize_rho_0 4 (by trivial)), (h_normalize_rho_1 4 (by trivial)), (h_normalize_rho_2 4 (by trivial)),
      (h_normalize_rho_0 5 (by trivial)), (h_normalize_rho_1 5 (by trivial)), (h_normalize_rho_2 5 (by trivial)),
      (h_normalize_rho_0 6 (by trivial)), (h_normalize_rho_1 6 (by trivial)), (h_normalize_rho_2 6 (by trivial)),
      (h_normalize_rho_0 7 (by trivial)), (h_normalize_rho_1 7 (by trivial)), (h_normalize_rho_2 7 (by trivial)),
      (h_normalize_rho_0 8 (by trivial)), (h_normalize_rho_1 8 (by trivial)), (h_normalize_rho_2 8 (by trivial)),
      (h_normalize_rho_0 9 (by trivial)), (h_normalize_rho_1 9 (by trivial)), (h_normalize_rho_2 9 (by trivial)),
      (h_normalize_rho_0 10 (by trivial)), (h_normalize_rho_1 10 (by trivial)), (h_normalize_rho_2 10 (by trivial)),
      (h_normalize_rho_0 11 (by trivial)), (h_normalize_rho_1 11 (by trivial)), (h_normalize_rho_2 11 (by trivial)),
      lookup_zero_rot (h_normalize_rho_3 0 (by trivial)), lookup_zero_rot (h_normalize_rho_4 0 (by trivial)), lookup_zero_rot (h_normalize_rho_5 0 (by trivial)),
      h_normalize_rho_3 1 (by trivial), h_normalize_rho_4 1 (by trivial), h_normalize_rho_5 1 (by trivial),
      h_normalize_rho_3 2 (by trivial), h_normalize_rho_4 2 (by trivial), h_normalize_rho_5 2 (by trivial),
      h_normalize_rho_3 3 (by trivial), h_normalize_rho_4 3 (by trivial), h_normalize_rho_5 3 (by trivial),
    ]
    simp [Decode.expr.eq_def, keccak_constants, mul_add, ←mul_assoc, ←pow_add]
    simp only [
      zmod_pow_shift_simps, add_assoc, ←Nat.cast_add,
      ←nat_shiftLeft_eq_mul_comm,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Nat.shiftLeft_xor_distrib,
      Nat.shiftLeft_and_distrib
    ]
    rewrite [
      separate_chi_decodes_12
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial)),
      separate_chi_decodes_24
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt,
      separate_chi_decodes_36
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt,
      separate_chi_decodes_48
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt,
      separate_chi_decodes_60
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt,
      separate_chi_decodes_72
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt,
      separate_chi_decodes_84
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt,
      separate_chi_decodes_96
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt,
      separate_chi_decodes_108
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt,
      separate_chi_decodes_120
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt,
      separate_chi_decodes_132
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt,
      separate_chi_decodes_144
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt,
      separate_chi_decodes_156
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt,
      separate_chi_decodes_168
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt,
      separate_chi_decodes_180
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt,
    ]
    simp only [normalize_bit_invert_normalize_4]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat (x := (c.get_advice _ _).val) (show 12 = BIT_COUNT*4 by simp [keccak_constants]),
      ←Normalize.normalize_unpacked_ofNat_toNat (x := bit_invert (c.get_advice _ _).val _) (show 12 = BIT_COUNT*4 by simp [keccak_constants])
    ]
    rewrite [
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    simp [to_cell_manager, h_to_cell_manager]
    rw [
      state_3_3 h_meets_constraints h_round (by omega),
      state_4_4_invert h_meets_constraints h_round (by omega),
      state_0_0 h_meets_constraints h_round (by omega),
      ←Normalize.normalize_unpacked_and,
      ←Normalize.normalize_unpacked_xor,
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask (by unfold Normalize.mask; omega))
    ]

  lemma chi_os'_3_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2690186458022863184501052609946142749758152333341729076955<P):
    (os' c round 3 1).val =
    Normalize.normalize_unpacked (
      rho_s_1_3 c round ^^^ (
        bit_invert (rho_s_2_4 c round) 64 &&&
        rho_s_3_0 c round
      )
    ) 64
  := by
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round' := Finset.mem_Icc.mp h_round
    have h_P': P ≥ 4096 := by omega
    simp [os', keccak_constants, list_ops, rho_pi_chi_cells, cell_manager_to_raw]
    have : 12 * round % c.n = 12 * round := by rw [Nat.mod_eq_of_lt (by omega)]
    have h_to_cell_manager: 12 * round + 11 < c.n := by omega
    have h_lookup_P: P ≥ 1756 := by omega
    have h_normalize_rho_0 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_78 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_1 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_79 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_2 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_75 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_3 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_83 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_4 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_84 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_5 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_80 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    try simp [fin_vals]
    rewrite [
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 4 (by trivial)) (h_normalize_rho_1 4 (by trivial)) (h_normalize_rho_2 4 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 5 (by trivial)) (h_normalize_rho_1 5 (by trivial)) (h_normalize_rho_2 5 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 6 (by trivial)) (h_normalize_rho_1 6 (by trivial)) (h_normalize_rho_2 6 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 7 (by trivial)) (h_normalize_rho_1 7 (by trivial)) (h_normalize_rho_2 7 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 8 (by trivial)) (h_normalize_rho_1 8 (by trivial)) (h_normalize_rho_2 8 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 9 (by trivial)) (h_normalize_rho_1 9 (by trivial)) (h_normalize_rho_2 9 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 10 (by trivial)) (h_normalize_rho_1 10 (by trivial)) (h_normalize_rho_2 10 (by trivial)),
      chi_base_1_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 11 (by trivial)) (h_normalize_rho_1 11 (by trivial)) (h_normalize_rho_2 11 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_3 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_4 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_5 0 (by trivial))),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 1 (by trivial)) (h_normalize_rho_4 1 (by trivial)) (h_normalize_rho_5 1 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 2 (by trivial)) (h_normalize_rho_4 2 (by trivial)) (h_normalize_rho_5 2 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 3 (by trivial)) (h_normalize_rho_4 3 (by trivial)) (h_normalize_rho_5 3 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 4 (by trivial)) (h_normalize_rho_4 4 (by trivial)) (h_normalize_rho_5 4 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 5 (by trivial)) (h_normalize_rho_4 5 (by trivial)) (h_normalize_rho_5 5 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 6 (by trivial)) (h_normalize_rho_4 6 (by trivial)) (h_normalize_rho_5 6 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 7 (by trivial)) (h_normalize_rho_4 7 (by trivial)) (h_normalize_rho_5 7 (by trivial)),
    ]
    rewrite [
      (h_normalize_rho_0 4 (by trivial)), (h_normalize_rho_1 4 (by trivial)), (h_normalize_rho_2 4 (by trivial)),
      (h_normalize_rho_0 5 (by trivial)), (h_normalize_rho_1 5 (by trivial)), (h_normalize_rho_2 5 (by trivial)),
      (h_normalize_rho_0 6 (by trivial)), (h_normalize_rho_1 6 (by trivial)), (h_normalize_rho_2 6 (by trivial)),
      (h_normalize_rho_0 7 (by trivial)), (h_normalize_rho_1 7 (by trivial)), (h_normalize_rho_2 7 (by trivial)),
      (h_normalize_rho_0 8 (by trivial)), (h_normalize_rho_1 8 (by trivial)), (h_normalize_rho_2 8 (by trivial)),
      (h_normalize_rho_0 9 (by trivial)), (h_normalize_rho_1 9 (by trivial)), (h_normalize_rho_2 9 (by trivial)),
      (h_normalize_rho_0 10 (by trivial)), (h_normalize_rho_1 10 (by trivial)), (h_normalize_rho_2 10 (by trivial)),
      (h_normalize_rho_0 11 (by trivial)), (h_normalize_rho_1 11 (by trivial)), (h_normalize_rho_2 11 (by trivial)),
      lookup_zero_rot (h_normalize_rho_3 0 (by trivial)), lookup_zero_rot (h_normalize_rho_4 0 (by trivial)), lookup_zero_rot (h_normalize_rho_5 0 (by trivial)),
      h_normalize_rho_3 1 (by trivial), h_normalize_rho_4 1 (by trivial), h_normalize_rho_5 1 (by trivial),
      h_normalize_rho_3 2 (by trivial), h_normalize_rho_4 2 (by trivial), h_normalize_rho_5 2 (by trivial),
      h_normalize_rho_3 3 (by trivial), h_normalize_rho_4 3 (by trivial), h_normalize_rho_5 3 (by trivial),
      h_normalize_rho_3 4 (by trivial), h_normalize_rho_4 4 (by trivial), h_normalize_rho_5 4 (by trivial),
      h_normalize_rho_3 5 (by trivial), h_normalize_rho_4 5 (by trivial), h_normalize_rho_5 5 (by trivial),
      h_normalize_rho_3 6 (by trivial), h_normalize_rho_4 6 (by trivial), h_normalize_rho_5 6 (by trivial),
      h_normalize_rho_3 7 (by trivial), h_normalize_rho_4 7 (by trivial), h_normalize_rho_5 7 (by trivial),
    ]
    simp [Decode.expr.eq_def, keccak_constants, mul_add, ←mul_assoc, ←pow_add]
    simp only [
      zmod_pow_shift_simps, add_assoc, ←Nat.cast_add,
      ←nat_shiftLeft_eq_mul_comm,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Nat.shiftLeft_xor_distrib,
      Nat.shiftLeft_and_distrib
    ]
    rewrite [
      separate_chi_decodes_12
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial)),
      separate_chi_decodes_24
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt,
      separate_chi_decodes_36
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt,
      separate_chi_decodes_48
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt,
      separate_chi_decodes_60
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt,
      separate_chi_decodes_72
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt,
      separate_chi_decodes_84
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt,
      separate_chi_decodes_96
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt,
      separate_chi_decodes_108
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt,
      separate_chi_decodes_120
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt,
      separate_chi_decodes_132
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt,
      separate_chi_decodes_144
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt,
      separate_chi_decodes_156
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt,
      separate_chi_decodes_168
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt,
      separate_chi_decodes_180
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt,
    ]
    simp only [normalize_bit_invert_normalize_4]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat (x := (c.get_advice _ _).val) (show 12 = BIT_COUNT*4 by simp [keccak_constants]),
      ←Normalize.normalize_unpacked_ofNat_toNat (x := bit_invert (c.get_advice _ _).val _) (show 12 = BIT_COUNT*4 by simp [keccak_constants])
    ]
    rewrite [
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    simp [to_cell_manager, h_to_cell_manager]
    rw [
      state_1_3 h_meets_constraints h_round (by omega),
      state_2_4_invert h_meets_constraints h_round (by omega),
      state_3_0 h_meets_constraints h_round (by omega),
      ←Normalize.normalize_unpacked_and,
      ←Normalize.normalize_unpacked_xor,
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask (by unfold Normalize.mask; omega))
    ]

  lemma chi_os'_3_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2690186458022863184501052609946142749758152333341729076955<P):
    (os' c round 3 2).val =
    Normalize.normalize_unpacked (
      rho_s_4_3 c round ^^^ (
        bit_invert (rho_s_0_4 c round) 64 &&&
        rho_s_1_0 c round
      )
    ) 64
  := by
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round' := Finset.mem_Icc.mp h_round
    have h_P': P ≥ 4096 := by omega
    simp [os', keccak_constants, list_ops, rho_pi_chi_cells, cell_manager_to_raw]
    have : 12 * round % c.n = 12 * round := by rw [Nat.mod_eq_of_lt (by omega)]
    have h_to_cell_manager: 12 * round + 11 < c.n := by omega
    have h_lookup_P: P ≥ 1756 := by omega
    have h_normalize_rho_0 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_83 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_1 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_84 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_2 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_80 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_3 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_88 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_4 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_89 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_5 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_85 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    try simp [fin_vals]
    rewrite [
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 8 (by trivial)) (h_normalize_rho_1 8 (by trivial)) (h_normalize_rho_2 8 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 9 (by trivial)) (h_normalize_rho_1 9 (by trivial)) (h_normalize_rho_2 9 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 10 (by trivial)) (h_normalize_rho_1 10 (by trivial)) (h_normalize_rho_2 10 (by trivial)),
      chi_base_2_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 11 (by trivial)) (h_normalize_rho_1 11 (by trivial)) (h_normalize_rho_2 11 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_3 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_4 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_5 0 (by trivial))),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 1 (by trivial)) (h_normalize_rho_4 1 (by trivial)) (h_normalize_rho_5 1 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 2 (by trivial)) (h_normalize_rho_4 2 (by trivial)) (h_normalize_rho_5 2 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 3 (by trivial)) (h_normalize_rho_4 3 (by trivial)) (h_normalize_rho_5 3 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 4 (by trivial)) (h_normalize_rho_4 4 (by trivial)) (h_normalize_rho_5 4 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 5 (by trivial)) (h_normalize_rho_4 5 (by trivial)) (h_normalize_rho_5 5 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 6 (by trivial)) (h_normalize_rho_4 6 (by trivial)) (h_normalize_rho_5 6 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 7 (by trivial)) (h_normalize_rho_4 7 (by trivial)) (h_normalize_rho_5 7 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 8 (by trivial)) (h_normalize_rho_4 8 (by trivial)) (h_normalize_rho_5 8 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 9 (by trivial)) (h_normalize_rho_4 9 (by trivial)) (h_normalize_rho_5 9 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 10 (by trivial)) (h_normalize_rho_4 10 (by trivial)) (h_normalize_rho_5 10 (by trivial)),
      chi_base_3_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 11 (by trivial)) (h_normalize_rho_4 11 (by trivial)) (h_normalize_rho_5 11 (by trivial)),
    ]
    rewrite [
      (h_normalize_rho_0 8 (by trivial)), (h_normalize_rho_1 8 (by trivial)), (h_normalize_rho_2 8 (by trivial)),
      (h_normalize_rho_0 9 (by trivial)), (h_normalize_rho_1 9 (by trivial)), (h_normalize_rho_2 9 (by trivial)),
      (h_normalize_rho_0 10 (by trivial)), (h_normalize_rho_1 10 (by trivial)), (h_normalize_rho_2 10 (by trivial)),
      (h_normalize_rho_0 11 (by trivial)), (h_normalize_rho_1 11 (by trivial)), (h_normalize_rho_2 11 (by trivial)),
      lookup_zero_rot (h_normalize_rho_3 0 (by trivial)), lookup_zero_rot (h_normalize_rho_4 0 (by trivial)), lookup_zero_rot (h_normalize_rho_5 0 (by trivial)),
      h_normalize_rho_3 1 (by trivial), h_normalize_rho_4 1 (by trivial), h_normalize_rho_5 1 (by trivial),
      h_normalize_rho_3 2 (by trivial), h_normalize_rho_4 2 (by trivial), h_normalize_rho_5 2 (by trivial),
      h_normalize_rho_3 3 (by trivial), h_normalize_rho_4 3 (by trivial), h_normalize_rho_5 3 (by trivial),
      h_normalize_rho_3 4 (by trivial), h_normalize_rho_4 4 (by trivial), h_normalize_rho_5 4 (by trivial),
      h_normalize_rho_3 5 (by trivial), h_normalize_rho_4 5 (by trivial), h_normalize_rho_5 5 (by trivial),
      h_normalize_rho_3 6 (by trivial), h_normalize_rho_4 6 (by trivial), h_normalize_rho_5 6 (by trivial),
      h_normalize_rho_3 7 (by trivial), h_normalize_rho_4 7 (by trivial), h_normalize_rho_5 7 (by trivial),
      h_normalize_rho_3 8 (by trivial), h_normalize_rho_4 8 (by trivial), h_normalize_rho_5 8 (by trivial),
      h_normalize_rho_3 9 (by trivial), h_normalize_rho_4 9 (by trivial), h_normalize_rho_5 9 (by trivial),
      h_normalize_rho_3 10 (by trivial), h_normalize_rho_4 10 (by trivial), h_normalize_rho_5 10 (by trivial),
      h_normalize_rho_3 11 (by trivial), h_normalize_rho_4 11 (by trivial), h_normalize_rho_5 11 (by trivial),
    ]
    simp [Decode.expr.eq_def, keccak_constants, mul_add, ←mul_assoc, ←pow_add]
    simp only [
      zmod_pow_shift_simps, add_assoc, ←Nat.cast_add,
      ←nat_shiftLeft_eq_mul_comm,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Nat.shiftLeft_xor_distrib,
      Nat.shiftLeft_and_distrib
    ]
    rewrite [
      separate_chi_decodes_12
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial)),
      separate_chi_decodes_24
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt,
      separate_chi_decodes_36
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt,
      separate_chi_decodes_48
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt,
      separate_chi_decodes_60
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt,
      separate_chi_decodes_72
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt,
      separate_chi_decodes_84
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt,
      separate_chi_decodes_96
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt,
      separate_chi_decodes_108
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt,
      separate_chi_decodes_120
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt,
      separate_chi_decodes_132
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt,
      separate_chi_decodes_144
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt,
      separate_chi_decodes_156
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt,
      separate_chi_decodes_168
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt,
      separate_chi_decodes_180
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt,
    ]
    simp only [normalize_bit_invert_normalize_4]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat (x := (c.get_advice _ _).val) (show 12 = BIT_COUNT*4 by simp [keccak_constants]),
      ←Normalize.normalize_unpacked_ofNat_toNat (x := bit_invert (c.get_advice _ _).val _) (show 12 = BIT_COUNT*4 by simp [keccak_constants])
    ]
    rewrite [
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    simp [to_cell_manager, h_to_cell_manager]
    rw [
      state_4_3 h_meets_constraints h_round (by omega),
      state_0_4_invert h_meets_constraints h_round (by omega),
      state_1_0 h_meets_constraints h_round (by omega),
      ←Normalize.normalize_unpacked_and,
      ←Normalize.normalize_unpacked_xor,
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask (by unfold Normalize.mask; omega))
    ]

  lemma chi_os'_3_3 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2690186458022863184501052609946142749758152333341729076955<P):
    (os' c round 3 3).val =
    Normalize.normalize_unpacked (
      rho_s_2_3 c round ^^^ (
        bit_invert (rho_s_3_4 c round) 64 &&&
        rho_s_4_0 c round
      )
    ) 64
  := by
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round' := Finset.mem_Icc.mp h_round
    have h_P': P ≥ 4096 := by omega
    simp [os', keccak_constants, list_ops, rho_pi_chi_cells, cell_manager_to_raw]
    have : 12 * round % c.n = 12 * round := by rw [Nat.mod_eq_of_lt (by omega)]
    have h_to_cell_manager: 12 * round + 11 < c.n := by omega
    have h_lookup_P: P ≥ 1756 := by omega
    have h_normalize_rho_0 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_93 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_1 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_94 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_2 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_90 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_3 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_98 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_4 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_99 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_5 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_95 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    try simp [fin_vals]
    rewrite [
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_0 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_1 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_2 0 (by trivial))),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 1 (by trivial)) (h_normalize_rho_1 1 (by trivial)) (h_normalize_rho_2 1 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 2 (by trivial)) (h_normalize_rho_1 2 (by trivial)) (h_normalize_rho_2 2 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 3 (by trivial)) (h_normalize_rho_1 3 (by trivial)) (h_normalize_rho_2 3 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 4 (by trivial)) (h_normalize_rho_1 4 (by trivial)) (h_normalize_rho_2 4 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 5 (by trivial)) (h_normalize_rho_1 5 (by trivial)) (h_normalize_rho_2 5 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 6 (by trivial)) (h_normalize_rho_1 6 (by trivial)) (h_normalize_rho_2 6 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 7 (by trivial)) (h_normalize_rho_1 7 (by trivial)) (h_normalize_rho_2 7 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 8 (by trivial)) (h_normalize_rho_1 8 (by trivial)) (h_normalize_rho_2 8 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 9 (by trivial)) (h_normalize_rho_1 9 (by trivial)) (h_normalize_rho_2 9 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 10 (by trivial)) (h_normalize_rho_1 10 (by trivial)) (h_normalize_rho_2 10 (by trivial)),
      chi_base_4_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 11 (by trivial)) (h_normalize_rho_1 11 (by trivial)) (h_normalize_rho_2 11 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_3 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_4 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_5 0 (by trivial))),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 1 (by trivial)) (h_normalize_rho_4 1 (by trivial)) (h_normalize_rho_5 1 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 2 (by trivial)) (h_normalize_rho_4 2 (by trivial)) (h_normalize_rho_5 2 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 3 (by trivial)) (h_normalize_rho_4 3 (by trivial)) (h_normalize_rho_5 3 (by trivial)),
    ]
    rewrite [
      lookup_zero_rot (h_normalize_rho_0 0 (by trivial)), lookup_zero_rot (h_normalize_rho_1 0 (by trivial)), lookup_zero_rot (h_normalize_rho_2 0 (by trivial)),
      (h_normalize_rho_0 1 (by trivial)), (h_normalize_rho_1 1 (by trivial)), (h_normalize_rho_2 1 (by trivial)),
      (h_normalize_rho_0 2 (by trivial)), (h_normalize_rho_1 2 (by trivial)), (h_normalize_rho_2 2 (by trivial)),
      (h_normalize_rho_0 3 (by trivial)), (h_normalize_rho_1 3 (by trivial)), (h_normalize_rho_2 3 (by trivial)),
      (h_normalize_rho_0 4 (by trivial)), (h_normalize_rho_1 4 (by trivial)), (h_normalize_rho_2 4 (by trivial)),
      (h_normalize_rho_0 5 (by trivial)), (h_normalize_rho_1 5 (by trivial)), (h_normalize_rho_2 5 (by trivial)),
      (h_normalize_rho_0 6 (by trivial)), (h_normalize_rho_1 6 (by trivial)), (h_normalize_rho_2 6 (by trivial)),
      (h_normalize_rho_0 7 (by trivial)), (h_normalize_rho_1 7 (by trivial)), (h_normalize_rho_2 7 (by trivial)),
      (h_normalize_rho_0 8 (by trivial)), (h_normalize_rho_1 8 (by trivial)), (h_normalize_rho_2 8 (by trivial)),
      (h_normalize_rho_0 9 (by trivial)), (h_normalize_rho_1 9 (by trivial)), (h_normalize_rho_2 9 (by trivial)),
      (h_normalize_rho_0 10 (by trivial)), (h_normalize_rho_1 10 (by trivial)), (h_normalize_rho_2 10 (by trivial)),
      (h_normalize_rho_0 11 (by trivial)), (h_normalize_rho_1 11 (by trivial)), (h_normalize_rho_2 11 (by trivial)),
      lookup_zero_rot (h_normalize_rho_3 0 (by trivial)), lookup_zero_rot (h_normalize_rho_4 0 (by trivial)), lookup_zero_rot (h_normalize_rho_5 0 (by trivial)),
      h_normalize_rho_3 1 (by trivial), h_normalize_rho_4 1 (by trivial), h_normalize_rho_5 1 (by trivial),
      h_normalize_rho_3 2 (by trivial), h_normalize_rho_4 2 (by trivial), h_normalize_rho_5 2 (by trivial),
      h_normalize_rho_3 3 (by trivial), h_normalize_rho_4 3 (by trivial), h_normalize_rho_5 3 (by trivial),
    ]
    simp [Decode.expr.eq_def, keccak_constants, mul_add, ←mul_assoc, ←pow_add]
    simp only [
      zmod_pow_shift_simps, add_assoc, ←Nat.cast_add,
      ←nat_shiftLeft_eq_mul_comm,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Nat.shiftLeft_xor_distrib,
      Nat.shiftLeft_and_distrib
    ]
    rewrite [
      separate_chi_decodes_12
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial)),
      separate_chi_decodes_24
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt,
      separate_chi_decodes_36
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt,
      separate_chi_decodes_48
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt,
      separate_chi_decodes_60
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt,
      separate_chi_decodes_72
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt,
      separate_chi_decodes_84
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt,
      separate_chi_decodes_96
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt,
      separate_chi_decodes_108
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt,
      separate_chi_decodes_120
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt,
      separate_chi_decodes_132
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt,
      separate_chi_decodes_144
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt,
      separate_chi_decodes_156
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt,
      separate_chi_decodes_168
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt,
      separate_chi_decodes_180
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt,
    ]
    simp only [normalize_bit_invert_normalize_4]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat (x := (c.get_advice _ _).val) (show 12 = BIT_COUNT*4 by simp [keccak_constants]),
      ←Normalize.normalize_unpacked_ofNat_toNat (x := bit_invert (c.get_advice _ _).val _) (show 12 = BIT_COUNT*4 by simp [keccak_constants])
    ]
    rewrite [
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    simp [to_cell_manager, h_to_cell_manager]
    rw [
      state_2_3 h_meets_constraints h_round (by omega),
      state_3_4_invert h_meets_constraints h_round (by omega),
      state_4_0 h_meets_constraints h_round (by omega),
      ←Normalize.normalize_unpacked_and,
      ←Normalize.normalize_unpacked_xor,
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask (by unfold Normalize.mask; omega))
    ]

  lemma chi_os'_3_4 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2690186458022863184501052609946142749758152333341729076955<P):
    (os' c round 3 4).val =
    Normalize.normalize_unpacked (
      rho_s_0_3 c round ^^^ (
        bit_invert (rho_s_1_4 c round) 64 &&&
        rho_s_2_0 c round
      )
    ) 64
  := by
    have h_n := n_range_of_meets_constraints h_meets_constraints
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_round' := Finset.mem_Icc.mp h_round
    have h_P': P ≥ 4096 := by omega
    simp [os', keccak_constants, list_ops, rho_pi_chi_cells, cell_manager_to_raw]
    have : 12 * round % c.n = 12 * round := by rw [Nat.mod_eq_of_lt (by omega)]
    have h_to_cell_manager: 12 * round + 11 < c.n := by omega
    have h_lookup_P: P ≥ 1756 := by omega
    have h_normalize_rho_0 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_98 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_1 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_99 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_2 (rot: ℕ) (h_rot: rot ≤ 11) := lookup_col_95 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_3 (rot: ℕ) (h_rot: rot ≤ 7) := lookup_col_103 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_4 (rot: ℕ) (h_rot: rot ≤ 7) := lookup_col_104 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    have h_normalize_rho_5 (rot: ℕ) (h_rot: rot ≤ 7) := lookup_col_100 h_meets_constraints h_lookup_P h_to_cell_manager h_round h_rot
    try simp [fin_vals]
    rewrite [
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 4 (by trivial)) (h_normalize_rho_1 4 (by trivial)) (h_normalize_rho_2 4 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 5 (by trivial)) (h_normalize_rho_1 5 (by trivial)) (h_normalize_rho_2 5 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 6 (by trivial)) (h_normalize_rho_1 6 (by trivial)) (h_normalize_rho_2 6 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 7 (by trivial)) (h_normalize_rho_1 7 (by trivial)) (h_normalize_rho_2 7 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 8 (by trivial)) (h_normalize_rho_1 8 (by trivial)) (h_normalize_rho_2 8 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 9 (by trivial)) (h_normalize_rho_1 9 (by trivial)) (h_normalize_rho_2 9 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 10 (by trivial)) (h_normalize_rho_1 10 (by trivial)) (h_normalize_rho_2 10 (by trivial)),
      chi_base_5_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_0 11 (by trivial)) (h_normalize_rho_1 11 (by trivial)) (h_normalize_rho_2 11 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (lookup_zero_rot (h_normalize_rho_3 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_4 0 (by trivial))) (lookup_zero_rot (h_normalize_rho_5 0 (by trivial))),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 1 (by trivial)) (h_normalize_rho_4 1 (by trivial)) (h_normalize_rho_5 1 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 2 (by trivial)) (h_normalize_rho_4 2 (by trivial)) (h_normalize_rho_5 2 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 3 (by trivial)) (h_normalize_rho_4 3 (by trivial)) (h_normalize_rho_5 3 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 4 (by trivial)) (h_normalize_rho_4 4 (by trivial)) (h_normalize_rho_5 4 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 5 (by trivial)) (h_normalize_rho_4 5 (by trivial)) (h_normalize_rho_5 5 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 6 (by trivial)) (h_normalize_rho_4 6 (by trivial)) (h_normalize_rho_5 6 (by trivial)),
      chi_base_6_3 h_meets_constraints (by simp [keccak_constants]; omega) (by rewrite [Nat.mod_eq_of_lt] <;> omega)
        (h_normalize_rho_3 7 (by trivial)) (h_normalize_rho_4 7 (by trivial)) (h_normalize_rho_5 7 (by trivial)),
    ]
    rewrite [
      (h_normalize_rho_0 4 (by trivial)), (h_normalize_rho_1 4 (by trivial)), (h_normalize_rho_2 4 (by trivial)),
      (h_normalize_rho_0 5 (by trivial)), (h_normalize_rho_1 5 (by trivial)), (h_normalize_rho_2 5 (by trivial)),
      (h_normalize_rho_0 6 (by trivial)), (h_normalize_rho_1 6 (by trivial)), (h_normalize_rho_2 6 (by trivial)),
      (h_normalize_rho_0 7 (by trivial)), (h_normalize_rho_1 7 (by trivial)), (h_normalize_rho_2 7 (by trivial)),
      (h_normalize_rho_0 8 (by trivial)), (h_normalize_rho_1 8 (by trivial)), (h_normalize_rho_2 8 (by trivial)),
      (h_normalize_rho_0 9 (by trivial)), (h_normalize_rho_1 9 (by trivial)), (h_normalize_rho_2 9 (by trivial)),
      (h_normalize_rho_0 10 (by trivial)), (h_normalize_rho_1 10 (by trivial)), (h_normalize_rho_2 10 (by trivial)),
      (h_normalize_rho_0 11 (by trivial)), (h_normalize_rho_1 11 (by trivial)), (h_normalize_rho_2 11 (by trivial)),
      lookup_zero_rot (h_normalize_rho_3 0 (by trivial)), lookup_zero_rot (h_normalize_rho_4 0 (by trivial)), lookup_zero_rot (h_normalize_rho_5 0 (by trivial)),
      h_normalize_rho_3 1 (by trivial), h_normalize_rho_4 1 (by trivial), h_normalize_rho_5 1 (by trivial),
      h_normalize_rho_3 2 (by trivial), h_normalize_rho_4 2 (by trivial), h_normalize_rho_5 2 (by trivial),
      h_normalize_rho_3 3 (by trivial), h_normalize_rho_4 3 (by trivial), h_normalize_rho_5 3 (by trivial),
      h_normalize_rho_3 4 (by trivial), h_normalize_rho_4 4 (by trivial), h_normalize_rho_5 4 (by trivial),
      h_normalize_rho_3 5 (by trivial), h_normalize_rho_4 5 (by trivial), h_normalize_rho_5 5 (by trivial),
      h_normalize_rho_3 6 (by trivial), h_normalize_rho_4 6 (by trivial), h_normalize_rho_5 6 (by trivial),
      h_normalize_rho_3 7 (by trivial), h_normalize_rho_4 7 (by trivial), h_normalize_rho_5 7 (by trivial),
    ]
    simp [Decode.expr.eq_def, keccak_constants, mul_add, ←mul_assoc, ←pow_add]
    simp only [
      zmod_pow_shift_simps, add_assoc, ←Nat.cast_add,
      ←nat_shiftLeft_eq_mul_comm,
      Normalize.normalize_unpacked_xor,
      Normalize.normalize_unpacked_idempotent,
      Normalize.normalize_unpacked_and,
      Nat.shiftLeft_xor_distrib,
      Nat.shiftLeft_and_distrib
    ]
    rewrite [
      separate_chi_decodes_12
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial)),
      separate_chi_decodes_24
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt
        separate_chi_decodes_24_lt,
      separate_chi_decodes_36
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt
        separate_chi_decodes_36_lt,
      separate_chi_decodes_48
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt
        separate_chi_decodes_48_lt,
      separate_chi_decodes_60
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt
        separate_chi_decodes_60_lt,
      separate_chi_decodes_72
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt
        separate_chi_decodes_72_lt,
      separate_chi_decodes_84
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt
        separate_chi_decodes_84_lt,
      separate_chi_decodes_96
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt
        separate_chi_decodes_96_lt,
      separate_chi_decodes_108
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt
        separate_chi_decodes_108_lt,
      separate_chi_decodes_120
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt
        separate_chi_decodes_120_lt,
      separate_chi_decodes_132
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt
        separate_chi_decodes_132_lt,
      separate_chi_decodes_144
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt
        separate_chi_decodes_144_lt,
      separate_chi_decodes_156
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt
        separate_chi_decodes_156_lt,
      separate_chi_decodes_168
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt
        separate_chi_decodes_168_lt,
      separate_chi_decodes_180
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        (lt_of_le_of_lt Normalize.normalize_unpacked_4_le (by trivial))
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt
        separate_chi_decodes_180_lt,
    ]
    simp only [normalize_bit_invert_normalize_4]
    simp only [
      ←Normalize.normalize_unpacked_ofNat_toNat (x := (c.get_advice _ _).val) (show 12 = BIT_COUNT*4 by simp [keccak_constants]),
      ←Normalize.normalize_unpacked_ofNat_toNat (x := bit_invert (c.get_advice _ _).val _) (show 12 = BIT_COUNT*4 by simp [keccak_constants])
    ]
    rewrite [
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_12_add, bitvec_toNat_shift_add 24 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_24_add, bitvec_toNat_shift_add 36 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_36_add, bitvec_toNat_shift_add 48 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_48_add, bitvec_toNat_shift_add 60 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_60_add, bitvec_toNat_shift_add 72 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_72_add, bitvec_toNat_shift_add 84 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_84_add, bitvec_toNat_shift_add 96 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_96_add, bitvec_toNat_shift_add 108 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_108_add, bitvec_toNat_shift_add 120 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_120_add, bitvec_toNat_shift_add 132 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_132_add, bitvec_toNat_shift_add 144 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_144_add, bitvec_toNat_shift_add 156 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_156_add, bitvec_toNat_shift_add 168 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_168_add, bitvec_toNat_shift_add 180 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
      Normalize.normalize_4_shift_180_add, bitvec_toNat_shift_add 192 (h := by trivial),
    ]
    simp [to_cell_manager, h_to_cell_manager]
    rw [
      state_0_3 h_meets_constraints h_round (by omega),
      state_1_4_invert h_meets_constraints h_round (by omega),
      state_2_0 h_meets_constraints h_round (by omega),
      ←Normalize.normalize_unpacked_and,
      ←Normalize.normalize_unpacked_xor,
      Nat.mod_eq_of_lt (lt_of_le_of_lt Normalize.normalize_unpacked_64_le_mask (by unfold Normalize.mask; omega))
    ]

end Keccak.Soundness

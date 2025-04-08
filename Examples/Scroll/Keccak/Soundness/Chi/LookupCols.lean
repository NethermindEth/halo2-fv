import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.Soundness.Chi.ChiBase
import Examples.Scroll.Keccak.Soundness.Chi.SeparateDecode
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.NormalizeRho.All
import Examples.Scroll.Keccak.Soundness.RhoRange.All
import Examples.Scroll.Keccak.Spec.Program
import Examples.Util

namespace Keccak.Soundness

  syntax "rho_pi_chi_2_normalize" ident : tactic
  macro_rules
    | `(tactic| rho_pi_chi_2_normalize $P:ident) => `(
    tactic| (
      have : $P ≥ 1756 := by omega
      simp [to_cell_manager, *, normalize_rho]
      rw [Nat.mod_eq_of_lt]
      exact lt_of_le_of_lt
        Normalize.normalize_unpacked_4_le
        (by omega)
    )
  )

  lemma lookup_col_70 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 70 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 35 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_71 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 71 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 36 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_72 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 72 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 37 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_73 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 73 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 38 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_74 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 74 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 39 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_75 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 75 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 40 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_76 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 76 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 41 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_77 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 77 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 42 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_78 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 78 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 43 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_79 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 79 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 44 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_80 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 80 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 45 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_81 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 81 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 46 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_82 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 82 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 47 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_83 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 83 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 48 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_84 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 84 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 49 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_85 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 85 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 50 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_86 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 86 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 51 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_87 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 87 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 52 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_88 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 88 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 53 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_89 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 89 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 54 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_90 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 90 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 55 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_91 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 91 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 56 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_92 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 92 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 57 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_93 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 93 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 58 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_94 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 94 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 59 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_95 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 95 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 60 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_96 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 96 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 61 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_97 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 97 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 62 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_98 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 98 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 63 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_99 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 11):
    (c.get_advice 99 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 64 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rho_pi_chi_2_normalize P

  lemma lookup_col_100 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 7):
    (c.get_advice 100 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 65 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rho_pi_chi_2_normalize P

  lemma lookup_col_101 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 7):
    (c.get_advice 101 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 66 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rho_pi_chi_2_normalize P

  lemma lookup_col_102 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 7):
    (c.get_advice 102 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 67 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rho_pi_chi_2_normalize P

  lemma lookup_col_103 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 7):
    (c.get_advice 103 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 68 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rho_pi_chi_2_normalize P

  lemma lookup_col_104 {c: ValidCircuit P P_Prime} [NeZero P] (h_meets_constraints: meets_constraints c) (h_P: P ≥ 1756) (h_n: 12*round + 11 < c.n) (h_round: round ∈ Finset.Icc 1 24) (h_rot: rot ≤ 7):
    (c.get_advice 104 ((12*round + rot)%c.n)).val = Normalize.normalize_unpacked (c.get_advice 69 ((12*round+rot)%c.n)).val 4
  := by match rot with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rho_pi_chi_2_normalize P

  lemma lookup_zero_rot {c: ValidCircuit P P_Prime} (h: (c.get_advice col ((12*round + 0)%c.n)).val = Normalize.normalize_unpacked (c.get_advice col' ((12*round+0)%c.n)).val 4):
    (c.get_advice col (12*round%c.n)).val = Normalize.normalize_unpacked (c.get_advice col' (12*round%c.n)).val 4
  := by simp_all


end Keccak.Soundness

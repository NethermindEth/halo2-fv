import Examples.Scroll.Keccak.Spec.FinVals
import Examples.Scroll.Keccak.Spec.KeccakConstants
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak

  lemma rho_pi_chi_location (c: ValidCircuit P P_Prime) (round: ℕ) (p: Fin 3) (i j: Fin 5) (idx: Fin rho_by_pi_num_word_parts):
    rho_pi_chi_cells c round p i j idx = c.get_advice (rho_pi_chi_column p i j idx) (rho_pi_chi_row c round j idx)
  := by
    simp [rho_pi_chi_cells, cell_manager_to_raw, rho_pi_chi_column, rho_pi_chi_row]
    obtain ⟨p, h_p⟩ := p
    obtain ⟨i, h_i⟩ := i
    obtain ⟨j, h_j⟩ := j
    obtain ⟨idx, h_idx⟩ := idx
    simp [keccak_constants] at h_idx ⊢
    congr 1
    . omega
    . congr 1
      omega

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_0 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 0,
      rho_pi_chi_column 1 j (2*i + 3 *j) 0
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_1 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 1,
      rho_pi_chi_column 1 j (2*i + 3 *j) 1
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_2 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 2,
      rho_pi_chi_column 1 j (2*i + 3 *j) 2
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_3 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 3,
      rho_pi_chi_column 1 j (2*i + 3 *j) 3
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_4 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 4,
      rho_pi_chi_column 1 j (2*i + 3 *j) 4
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_5 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 5,
      rho_pi_chi_column 1 j (2*i + 3 *j) 5
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_6 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 6,
      rho_pi_chi_column 1 j (2*i + 3 *j) 6
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_7 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 7,
      rho_pi_chi_column 1 j (2*i + 3 *j) 7
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_8 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 8,
      rho_pi_chi_column 1 j (2*i + 3 *j) 8
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_9 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 9,
      rho_pi_chi_column 1 j (2*i + 3 *j) 9
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_10 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 10,
      rho_pi_chi_column 1 j (2*i + 3 *j) 10
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_11 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 11,
      rho_pi_chi_column 1 j (2*i + 3 *j) 11
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_12 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 12,
      rho_pi_chi_column 1 j (2*i + 3 *j) 12
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_13 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 13,
      rho_pi_chi_column 1 j (2*i + 3 *j) 13
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_14 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 14,
      rho_pi_chi_column 1 j (2*i + 3 *j) 14
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }

  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_15 (i j):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) 15,
      rho_pi_chi_column 1 j (2*i + 3 *j) 15
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    rewrite [List.mem_iff_get]
    fin_cases j <;> fin_cases i
    all_goals {
      simp [Lookups.Normalize_4.normalize_4_column_pairs, rho_pi_chi_column, keccak_constants, fin_vals]
      decide
    }


  lemma rho_pi_chi_cells_col_0_1_in_normalize_4_cols (i j) (idx):
    (
      rho_pi_chi_column 0 j (2*i + 3*j) idx,
      rho_pi_chi_column 1 j (2*i + 3 *j) idx
    ) ∈ Lookups.Normalize_4.normalize_4_column_pairs
  := by
    obtain ⟨idx, h_idx⟩ := idx
    simp [keccak_constants] at h_idx
    match idx with
      | 0 => exact rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_0 i j
      | 1 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_1 i j <;> simp only [fin_vals]
      | 2 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_2 i j <;> simp only [fin_vals]
      | 3 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_3 i j <;> simp only [fin_vals]
      | 4 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_4 i j <;> simp only [fin_vals]
      | 5 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_5 i j <;> simp only [fin_vals]
      | 6 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_6 i j <;> simp only [fin_vals]
      | 7 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_7 i j <;> simp only [fin_vals]
      | 8 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_8 i j <;> simp only [fin_vals]
      | 9 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_9 i j <;> simp only [fin_vals]
      | 10 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_10 i j <;> simp only [fin_vals]
      | 11 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_11 i j <;> simp only [fin_vals]
      | 12 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_12 i j <;> simp only [fin_vals]
      | 13 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_13 i j <;> simp only [fin_vals]
      | 14 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_14 i j <;> simp only [fin_vals]
      | 15 => convert rho_pi_chi_cells_col_0_1_in_normalize_4_cols_idx_15 i j <;> simp only [fin_vals]
      | x+16 => omega

end Keccak

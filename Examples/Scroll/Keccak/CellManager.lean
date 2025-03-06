import Examples.Scroll.Keccak.Attributes
import Examples.Scroll.Keccak.Extraction
import Examples.Scroll.Keccak.Util

namespace Keccak
  def cell_manager (c: ValidCircuit P P_Prime) (round idx: ℕ) :=
    c.get_advice_wrapped (7 + idx/12) (12*round) (idx % 12) -- TODO use get_num_rows_per_round

  def cell_manager_column (idx: ℕ) := 7 + idx / 12
  def cell_manager_row (c: ValidCircuit P P_Prime) (round idx: ℕ) := (12*round + (idx%12)) % c.n

  lemma cell_manager_to_col_row: cell_manager c round idx = c.get_advice (cell_manager_column idx) (cell_manager_row c round idx) := rfl

  lemma cell_manager_to_raw: cell_manager c round idx = c.get_advice (7 + idx/12) (((12*round) + (idx % 12)) % c.n) := by
    rfl

  lemma get_advice_with_rot_to_cell_manager (c: ValidCircuit P P_Prime) (h_range: row + rot < c.n) (h_col: 7 ≤ col):
    c.get_advice col ((row + rot) % c.n) =
    cell_manager c (round := (row+rot)/12) (idx := 12*(col-7)+((row+rot)%12))
  := by
    simp only [cell_manager_to_raw, Nat.add_mod_mod, Nat.mod_eq_of_lt h_range]
    congr
    refine (Nat.sub_eq_iff_eq_add' h_col).mp ?_
    refine Eq.symm (Nat.div_eq_of_lt_le ?_ ?_)
    simp [mul_comm 12]
    rewrite [add_mul, mul_comm 12]
    simp [Nat.mod_lt]
    simp [Nat.add_mod _ (row+rot) 12]
    simp [add_comm, Nat.mod_add_div, Nat.mod_eq_of_lt h_range]

  lemma get_advice_in_round_to_cell_manager_zero_rot (h_col: 7 ≤ col) (h_range: 12*round < c.n):
    c.get_advice col (12*round) =
    cell_manager c round (12*(col-7))
  := by
    simp only [cell_manager_to_raw]
    rewrite [Nat.mul_div_cancel_left (col-7) (by trivial)]
    simp [h_col, Nat.mod_eq_of_lt h_range]

  @[to_cell_manager] lemma get_advice_in_round_to_cell_manager_zero_rot' (h_col: 7 ≤ col) (h_range: 12*round + 11 < c.n):
    c.get_advice col (12*round) =
    cell_manager c round (12*(col-7))
  := by
    rw [get_advice_in_round_to_cell_manager_zero_rot]
    assumption
    linarith

  @[to_cell_manager] lemma get_advice_in_round_to_cell_manager_zero_rot_mod (h_col: 7 ≤ col) (h_range: (12*round + 11 < c.n)):
    c.get_advice col ((12*round) % c.n) =
    cell_manager c round (12*(col-7))
  := by
    rw [Nat.mod_eq_of_lt, get_advice_in_round_to_cell_manager_zero_rot]
    assumption
    linarith
    linarith

  @[to_cell_manager] lemma get_advice_in_round_to_cell_manager_with_rot (h_col: 7 ≤ col) (h_range: 12*round + 11 < c.n) (h_rot: rot < 12):
    c.get_advice col ((12*round + rot) % c.n) =
    cell_manager c round (12*(col-7)+rot)
  := by
    have h_rot_range : 12*round + rot < c.n := by linarith
    simp [get_advice_with_rot_to_cell_manager, *]
    simp [Nat.mul_add_mod, Nat.mod_eq_of_lt h_rot]
    congr
    simp [Nat.mul_add_div, Nat.div_eq_zero_iff, h_rot]

  -- @[to_cell_manager] lemma get_advice_in_round_to_cell_manager_with_negative_rot (h_col: 7 ≤ col) (h_range: 12*round + 11 < c.n) (h_rot: rot < 12) (h_rot': rot > 0) (h_round_lower: round > 0):
  --   c.get_advice col ((12*round + c.n - rot % c.n) % c.n) =
  --   cell_manager c (round-1) (12*(col-6)-rot)
  -- := by
  --   rewrite [cell_manager_to_raw]
  --   congr
  --   rewrite [←Nat.sub_eq_iff_eq_add]
  --   have h_col: col-7+7 = col := Nat.sub_add_cancel h_col
  --   have h_col': col-6 = col-7+1 := by exact Nat.sub_eq_of_eq_add (id (Eq.symm h_col))
  --   rewrite [h_col']
  --   rewrite [←h_col]
  --   generalize h: col-7 = col'
  --   simp [mul_add]
  --   rewrite [Nat.add_sub_assoc (le_of_lt h_rot) (12*col'), Nat.add_div, ite_cond_eq_false, add_zero]

  @[to_cell_manager] lemma get_advice_wrapped_to_cell_manager (h_col: 7 ≤ col) (h_range: 12*round + 11 < c.n) (h_rot: rot < 12):
    c.get_advice_wrapped col (12*round) rot =
    cell_manager c round (12*(col-7)+rot)
  := by
    simp only [ValidCircuit.get_advice_wrapped, get_advice_in_round_to_cell_manager_with_rot, *]

end Keccak




-- cell_manager c round idx = c.get_advice (7 + idx/12) (((12*(round+1)) + (idx % 12)) % c.n)
-- requires: 12*(round+1) + (idx % 12) < c.n
-- col = 7 + idx/12
--  col - 7 = idx/12
--   12 * (col - 7) = idx - (idx % 12)
-- row = (((12*(round+1)) + (idx % 12)) % c.n)
--  row = ((12*(round+1)) + (idx % 12))
--
-- requires 12 ≤ row
-- round = (row/12)-1
-- idx = 12*a+b, b<12
-- a = col - 7
-- b = row % 12

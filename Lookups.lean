-- This module serves as the root of the `Lookups` library.
-- Import modules here that should be built as part of the library.
import «Lookups».Basic

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

namespace LookupExamples.Table

structure Circuit (P: ℕ) (P_Prime: Nat.Prime P) :=
  Advice: ℕ → ℕ → ZMod P
  Fixed: ℕ → ℕ → ZMod P
  Instance: ℕ → ℕ → ZMod P
  Selector: ℕ → ℕ → ZMod P
variable {P: ℕ} {P_Prime: Nat.Prime P}

-- REGION: load range-check table
-- REGION: load range-check table

-- REGION: load range-check table
-- REGION: load range-check table

-- REGION: Assign value for simple range check
-- REGION: Assign value for simple range check

-- REGION: Assign value for lookup range check
-- REGION: Assign value for lookup range check
def all_copy_constraints (c: Circuit P P_Prime): Prop := true
def selector_func_col_0 : ℕ → ZMod P :=
  λ row => match row with
    | _+1 => 0
    | _ => 1
def selector_func_col_1 : ℕ → ZMod P :=
  λ row => match row with
    | _+2 => 0
    | _+1 => 1
    | _ => 0
def selector_func : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => selector_func_col_0 row
    | 1 => selector_func_col_1 row
    | _ => 0
def fixed_func_col_0 : ℕ → ZMod P :=
  λ row => match row with
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 4
    | 4 => 5
    | 5 => 6
    | 6 => 7
    | 7 => 8
    | 8 => 9
    | 9 => 10
    | 10 => 11
    | 11 => 12
    | 12 => 13
    | 13 => 14
    | 14 => 15
    | 15 => 16
    | 16 => 17
    | 17 => 18
    | 18 => 19
    | _ => 0
def fixed_func_col_1 : ℕ → ZMod P :=
  λ row => match row with
    | 0 => 2
    | 1 => 4
    | 2 => 6
    | 3 => 8
    | 4 => 10
    | 5 => 12
    | 6 => 14
    | 7 => 16
    | 8 => 18
    | 9 => 20
    | 10 => 22
    | 11 => 24
    | 12 => 26
    | 13 => 28
    | 14 => 30
    | 15 => 32
    | 16 => 34
    | 17 => 36
    | 18 => 38
    | _ => 0
def fixed_func : ℕ → ℕ → ZMod P :=
  λ col row => match col with
    | 0 => fixed_func_col_0 row
    | 1 => fixed_func_col_1 row
    | _ => 0
------GATES-------
def gate_0 (c: Circuit P P_Prime): Prop := ∀ row : ℕ,   c.Selector 0 row * (((((((c.Advice 0 (row) * (1 - c.Advice 0 (row))) * (0x2 - c.Advice 0 (row))) * (0x3 - c.Advice 0 (row))) * (0x4 - c.Advice 0 (row))) * (0x5 - c.Advice 0 (row))) * (0x6 - c.Advice 0 (row))) * (0x7 - c.Advice 0 (row))) = 0
def all_gates (c: Circuit P P_Prime): Prop := gate_0 c
def meets_constraints (c: Circuit P P_Prime): Prop := c.Selector = selector_func ∧ all_gates c ∧ all_copy_constraints c ∧ c.Fixed = fixed_func
end LookupExamples.Table
-- !!Lookups!!: [
--     Argument {
--         input_expressions: [
--             Product(
--                 Selector(
--                     Selector(
--                         1,
--                         false,
--                     ),
--                 ),
--                 Advice {
--                     query_index: 0,
--                     column_index: 0,
--                     rotation: Rotation(
--                         0,
--                     ),
--                 },
--             ),
--         ],
--         table_expressions: [
--             Fixed {
--                 query_index: 0,
--                 column_index: 0,
--                 rotation: Rotation(
--                     0,
--                 ),
--             },
--         ],
--     },
--     Argument {
--         input_expressions: [
--             Sum(
--                 Product(
--                     Selector(
--                         Selector(
--                             1,
--                             false,
--                         ),
--                     ),
--                     Advice {
--                         query_index: 0,
--                         column_index: 0,
--                         rotation: Rotation(
--                             0,
--                         ),
--                     },
--                 ),
--                 Constant(
--                     0x1,
--                 ),
--             ),
--         ],
--         table_expressions: [
--             Fixed {
--                 query_index: 1,
--                 column_index: 1,
--                 rotation: Rotation(
--                     0,
--                 ),
--             },
--         ],
--     },
-- ]
-- !!Shuffles!!: []

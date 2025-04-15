import Examples.Scroll.Keccak.Lookups.PackTable.Lookups
import Examples.Scroll.Keccak.MeetsConstraints
import Examples.Scroll.Keccak.ProgramProofs.Absorb
import Examples.Scroll.Keccak.ProgramProofs.ProcessInputs
import Examples.Scroll.Keccak.Soundness.Normalize
import Examples.Scroll.Keccak.Soundness.Util
import Examples.Scroll.Keccak.Spec.FinVals

namespace Keccak.Soundness

  lemma initial_s_non_absorb_position {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_pos: (y,x) ∉ absorb_positions):
    (s c 1 y x).val = UInt64_to_unpacked_Nat (0)
  := by
    have h_absorb_gate := Proofs.absorb_gate_of_meets_constraints h_meets_constraints y x 0 (by trivial)
    simp [absorb_gate, h_pos, continue_hash, start_new_hash] at h_absorb_gate
    have h_fixed := fixed_of_meets_constraints h_meets_constraints
    simp [ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1] at h_absorb_gate
    rewrite [h_absorb_gate]
    simp [UInt64_to_unpacked_Nat]

  set_option maxHeartbeats 400000
  lemma initial_s_absorb_position {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: P > Normalize.mask) (h_pos: (y,x) ∈ absorb_positions):
    (s c 1 y x).val = UInt64_to_unpacked_Nat (
      UInt64.ofBitVec (
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 79).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 78).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 77).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 76).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 75).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 74).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 73).val ++
        BitVec.ofNat 8 (cell_manager c (a_slice y x + 1) 72).val
      )
    )
  := by
    unfold Normalize.mask at h_P
    have h_absorb_gate := Proofs.absorb_gate_of_meets_constraints h_meets_constraints y x 0 (by trivial)
    simp [absorb_gate, h_pos, continue_hash, start_new_hash] at h_absorb_gate
    have h_fixed := fixed_of_meets_constraints h_meets_constraints
    simp [ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1] at h_absorb_gate
    rewrite [←h_absorb_gate]
    have h_input_bytes := Proofs.input_bytes_of_meets_constraints h_meets_constraints (a_slice y x + 1) (by {
      unfold a_slice
      apply Finset.mem_Icc.mpr
      simp
      unfold absorb_positions at h_pos
      aesop (config := {warnOnNonterminal := false}) <;> simp [fin_vals]
    })
    simp [
      input_bytes, keccak_constants, Transform.split_expr, Split.expr, Split.expr_res, word_parts_known,
      Split.constraint, packed_parts
    ] at h_input_bytes
    rewrite [←h_input_bytes.1]
    have h_cell_0 := h_input_bytes.2.1
    have h_cell_1 := h_input_bytes.2.2.1
    have h_cell_2 := h_input_bytes.2.2.2.1
    have h_cell_3 := h_input_bytes.2.2.2.2.1
    have h_cell_4 := h_input_bytes.2.2.2.2.2.1
    have h_cell_5 := h_input_bytes.2.2.2.2.2.2.1
    have h_cell_6 := h_input_bytes.2.2.2.2.2.2.2.1
    have h_cell_7 := h_input_bytes.2.2.2.2.2.2.2.2
    rewrite [
      Lookups.PackTable.apply_transform_table h_cell_0 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_1 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_2 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_3 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_4 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_5 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_6 (by omega),
      Lookups.PackTable.apply_transform_table h_cell_7 (by omega),
    ]
    have h_table (x y: ZMod P) (h: ∃ lookup_row, Lookups.PackTable.transform_table P lookup_row = (x, y)):
      y.val < 256
    := by
      unfold Lookups.PackTable.transform_table at h
      obtain ⟨row, h_row⟩ := h
      split_ifs at h_row
      . simp at h_row
        rewrite [←h_row.2]
        simp
        rewrite [Nat.mod_eq_of_lt (by omega)]
        assumption
      . simp at h_row
        rewrite [←h_row.2]
        simp
    have h_byte (x: ℕ) (h: x < 256): x = (BitVec.ofNat 8 x).toNat := by
      simp (disch := omega) [Nat.mod_eq_of_lt]
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    simp [
      Decode.expr, keccak_constants, mul_add,
      ←mul_assoc, ZMod.val_add, ZMod.val_mul,
      Lookups.PackTable.into_bits.eq_def, list_ops,
      Lookups.PackTable.pack.eq_def, Lookups.PackTable.pack_with_base.eq_def,
      zmod_pow_simps, add_mul
    ]
    have : ZMod.val (n := P) 8 = 2^3 := by
      rewrite [zmod_val_ofNat_of_lt]
      . decide
      . exact lt_of_le_of_lt (by trivial) h_P
    rewrite [this]; clear this
    have : ZMod.val (n := P) 16777216 = 2^24 := by
      rewrite [zmod_val_ofNat_of_lt]
      . decide
      . exact lt_of_le_of_lt (by trivial) h_P
    rewrite [this]; clear this
    simp only [
      ←pow_add, ←nat_shiftLeft_eq_mul_comm, Nat.reduceAdd,
      ←Nat.shiftLeft_eq, ←Nat.shiftLeft_add
    ]
    have h_mod (a: ℕ): a%2 ≤ 1 := by omega
    have h_mul (a b: ℕ) : a % 2 * b ≤ b := by
      apply le_trans (b := 1*b)
      . apply Nat.mul_le_mul
        . exact h_mod _
        . simp
      . simp
    rewrite [Nat.mod_eq_of_lt]
    . simp [UInt64_to_unpacked_Nat, ←Nat.and_one_is_mod]
      set x1 := (cell_manager c (a_slice y x + 1) 72).val
      set x2 := (cell_manager c (a_slice y x + 1) 73).val
      set x3 := (cell_manager c (a_slice y x + 1) 74).val
      set x4 := (cell_manager c (a_slice y x + 1) 75).val
      set x5 := (cell_manager c (a_slice y x + 1) 76).val
      set x6 := (cell_manager c (a_slice y x + 1) 77).val
      set x7 := (cell_manager c (a_slice y x + 1) 78).val
      set x8 := (cell_manager c (a_slice y x + 1) 79).val
      rewrite [show x1 = (BitVec.setWidth 192 (BitVec.ofNat 8 x1)).toNat by {
        simp [x1]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_0),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_0) (by decide))
        ]
      }]
      rewrite [show x2 = (BitVec.setWidth 192 (BitVec.ofNat 8 x2)).toNat by {
        simp [x2]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_1),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_1) (by decide))
        ]
      }]
      rewrite [show x3 = (BitVec.setWidth 192 (BitVec.ofNat 8 x3)).toNat by {
        simp [x3]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_2),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_2) (by decide))
        ]
      }]
      rewrite [show x4 = (BitVec.setWidth 192 (BitVec.ofNat 8 x4)).toNat by {
        simp [x4]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_3),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_3) (by decide))
        ]
      }]
      rewrite [show x5 = (BitVec.setWidth 192 (BitVec.ofNat 8 x5)).toNat by {
        simp [x5]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_4),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_4) (by decide))
        ]
      }]
      rewrite [show x6 = (BitVec.setWidth 192 (BitVec.ofNat 8 x6)).toNat by {
        simp [x6]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_5),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_5) (by decide))
        ]
      }]
      rewrite [show x7 = (BitVec.setWidth 192 (BitVec.ofNat 8 x7)).toNat by {
        simp [x7]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_6),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_6) (by decide))
        ]
      }]
      rewrite [show x8 = (BitVec.setWidth 192 (BitVec.ofNat 8 x8)).toNat by {
        simp [x8]
        rw [
          Nat.mod_eq_of_lt (h_table _ _ h_cell_7),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (h_table _ _ h_cell_7) (by decide))
        ]
      }]
      rewrite [show 128 = (128#192).toNat by decide]
      have (a: ℕ) : a / 64 = a / (64#192).toNat := by congr
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _]
      have (a: ℕ) : a / 32 = a / (32#192).toNat := by congr
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _]
      have (a: ℕ) : a / 16 = a / (16#192).toNat := by congr
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _]
      have (a: ℕ) : a / 8 = a / (8#192).toNat := by congr
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _]
      rewrite [show 4 = (4#192).toNat by decide]
      have (a: ℕ) : a / 2 = a / (2#192).toNat := by congr
      rewrite [this _, this _, this _, this _, this _, this _, this _, this _]
      rewrite [show 1 = (1#192).toNat by decide]
      simp only [←BitVec.toNat_udiv, ←BitVec.toNat_and]
      have h_x1: x1 < 256 := by
        simp [x1]
        exact h_table _ _ h_cell_0
      have h_x2: x2 < 256 := by
        simp [x2]
        exact h_table _ _ h_cell_1
      have h_x3: x3 < 256 := by
        simp [x3]
        exact h_table _ _ h_cell_2
      have h_x4: x4 < 256 := by
        simp [x4]
        exact h_table _ _ h_cell_3
      have h_x5: x5 < 256 := by
        simp [x5]
        exact h_table _ _ h_cell_4
      have h_x6: x6 < 256 := by
        simp [x6]
        exact h_table _ _ h_cell_5
      have h_x7: x7 < 256 := by
        simp [x7]
        exact h_table _ _ h_cell_6
      have h_x8: x8 < 256 := by
        simp [x8]
        exact h_table _ _ h_cell_7
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 189 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 186 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 183 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 180 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 177 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 174 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 171 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 168 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 189 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 186 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 183 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 180 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 177 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 174 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 171 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 168).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x8]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 165 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 162 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 159 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 156 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 153 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 150 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 147 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 144 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 165 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 162 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 159 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 156 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 153 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 150 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 147 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 144).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x7]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 141 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 138 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 135 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 132 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 129 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 126 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 123 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 120 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 141 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 138 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 135 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 132 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 129 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 126 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 123 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 120).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x6]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 117 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 114 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 111 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 108 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 105 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 102 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 99 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 96 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 117 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 114 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 111 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 108 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 105 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 102 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 99 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 96).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x5]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 93 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 90 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 87 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 84 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 81 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 78 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 75 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 72 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 93 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 90 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 87 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 84 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 81 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 78 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 75 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 72).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x4]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 69 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 66 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 63 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 60 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 57 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 54 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 51 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 48 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 69 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 66 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 63 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 60 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 57 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 54 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 51 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 48).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x3]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 45 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 42 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 39 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 36 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 33 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 30 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 27 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat <<< 24 =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 45 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 42 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 39 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 36 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 33 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 30 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 27 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192) <<< 24).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mul _ _)) _
        decide
      rewrite [this _ h_x2]; clear this
      have (a: ℕ) (h: a < 256):
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192).toNat <<< 21 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192).toNat <<< 18 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192).toNat <<< 15 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192).toNat <<< 12 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192).toNat <<< 9 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192).toNat <<< 6 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192).toNat <<< 3 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192).toNat =
        ((BitVec.setWidth 192 (BitVec.ofNat 8 a) / 128#192 &&& 1#192) <<< 21 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 64#192 &&& 1#192) <<< 18 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 32#192 &&& 1#192) <<< 15 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 16#192 &&& 1#192) <<< 12 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 8#192 &&& 1#192) <<< 9 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 4#192 &&& 1#192) <<< 6 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) / 2#192 &&& 1#192) <<< 3 +
        (BitVec.setWidth 192 (BitVec.ofNat 8 a) &&& 1#192)).toNat
      := by
        simp
        rw [Nat.mod_eq_of_lt (a := _ + _)]
        simp [Nat.shiftLeft_eq]
        convert lt_of_le_of_lt (
          Nat.add_le_add (
            Nat.add_le_add (
              Nat.add_le_add (
                Nat.add_le_add (
                  Nat.add_le_add (
                    Nat.add_le_add
                      (Nat.add_le_add
                        (h_mul _ _)
                      (h_mul _ _))
                    (h_mul _ _))
                  (h_mul _ _))
                (h_mul _ _))
              (h_mul _ _))
            (h_mul _ _))
          (h_mod _)) _
        decide
      rewrite [this _ h_x1]; clear this
      rewrite [
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_add_of_and_eq_zero (by bv_decide),
        ←BitVec.toNat_eq
      ]
      simp [list_ops]
      rewrite [
        Nat.mod_eq_of_lt h_x1,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x1 (by decide)),
        Nat.mod_eq_of_lt h_x2,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x2 (by decide)),
        Nat.mod_eq_of_lt h_x3,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x3 (by decide)),
        Nat.mod_eq_of_lt h_x4,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x4 (by decide)),
        Nat.mod_eq_of_lt h_x5,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x5 (by decide)),
        Nat.mod_eq_of_lt h_x6,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x6 (by decide)),
        Nat.mod_eq_of_lt h_x7,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x7 (by decide)),
        Nat.mod_eq_of_lt h_x8,
        Nat.mod_eq_of_lt (lt_of_lt_of_le h_x8 (by decide)),
      ]
      bv_decide
    . apply lt_of_le_of_lt _ h_P
      simp [Nat.shiftLeft_eq]
      convert Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add
                    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _))
                    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
                  (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
                (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
              (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
            (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)))
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h_mul _ _) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mul _ _)) (h_mod _))


end Keccak.Soundness

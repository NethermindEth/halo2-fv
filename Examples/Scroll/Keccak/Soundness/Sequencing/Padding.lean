import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.ProgramProofs.LengthAndDataRlc
import Examples.Scroll.Keccak.ProgramProofs.Padding
import Examples.Scroll.Keccak.ProgramProofs.ProcessInputs

namespace Keccak.Soundness

  def padding (c: ValidCircuit P P_Prime) (n: ℕ): Bool :=
    (is_paddings c (n/8+1) n).val = 1
  def input_rlc (c: ValidCircuit P P_Prime) (n: ℕ): ZMod P :=
    data_rlc c (get_num_rows_per_round*(n/8+1)+NUM_BYTES_PER_WORD-(n%8+1))

  -- def partial_length (c: ValidCircuit P P_Prime) (n: ℕ) : ZMod P :=
  --   match n with
  --     | 0 => length c 12
  -- data_rlc c 20 = 0
  -- example : input_rlc c 0 = data_rlc c 19 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 1 = data_rlc c 18 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 2 = data_rlc c 17 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 3 = data_rlc c 16 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 4 = data_rlc c 15 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 5 = data_rlc c 14 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 6 = data_rlc c 13 := by simp [input_rlc, keccak_constants]
  -- example : input_rlc c 7 = data_rlc c 12 := by simp [input_rlc, keccak_constants]
  -- data_rlc c 32 = data_rlc 12
  -- example : input_rlc c 8 = data_rlc c 31 := by simp [input_rlc, keccak_constants]

  -- example : intermediate_data_rlc c ⟨2, sorry⟩ = sorry := by simp [intermediate_data_rlc, keccak_constants]
  -- data_rlc c 19 = data_rlc c 20 * challenge + input_bytes 1 [0] = 0*challenge + input_bytes 1 [0] = input_bytes 1 [0]
  -- data_rlc c 18 = data_rlc c 19 * challenge + input_bytes 1 [1] = input_bytes 1 [0] * challenge + input_bytes 1 [1]
  -- data_rlc c 17 = data_rlc c 18 * challenge + input_bytes 1 [2] = input_bytes 1 [0] * challenge^2 + input_bytes 1 [1] * challenge + input_bytes 1 [2]
  --data_rlc 31 = input_bytes 1 [6] * c^2 + input_bytes 1 [7] * c + input_bytes 2 [0]


  def input_bytes_sublist (c: ValidCircuit P P_Prime) (n: ℕ): List (ZMod P) :=
    ((List.range ((n/8)+1))
      |>.flatMap λ idx => (input_bytes c (idx+1)).1.map (λ (_,x) => x))
      |>.take n

  lemma input_bytes_len (h_byte: byte < 8):
    byte < (input_bytes c round).1.length
  := by
    simp [input_bytes.eq_def, Transform.split_expr.eq_def, Split.expr_res.eq_def, word_parts_known, keccak_constants, h_byte]

  def input_bytes_sublist_calc (c: ValidCircuit P P_Prime) (n: ℕ): List (ZMod P) :=
    List.take n [
      ((input_bytes c 1).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 1).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 2).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 3).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 4).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 5).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 6).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 7).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 8).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 9).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 10).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 11).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 12).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 13).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 14).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 15).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 16).1[7]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[0]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[1]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[2]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[3]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[4]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[5]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[6]'(input_bytes_len (by trivial))).2,
      ((input_bytes c 17).1[7]'(input_bytes_len (by trivial))).2
    ]

  lemma unfold_input_bytes_round (round):
    (input_bytes c round).1 = [
      (input_bytes c round).1[0]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[1]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[2]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[3]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[4]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[5]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[6]'(input_bytes_len (by trivial)),
      (input_bytes c round).1[7]'(input_bytes_len (by trivial)),
    ]
  := by simp [input_bytes.eq_def, Transform.split_expr, Split.expr_res, keccak_constants, word_parts_known]

  lemma input_bytes_sublist_eq_calc_10 (h_n: n < 10):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    match n with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [unfold_input_bytes_round 1, unfold_input_bytes_round 2]
        rfl


  lemma input_bytes_sublist_eq_calc_20 (h_n: n < 20):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 10; exact input_bytes_sublist_eq_calc_10 h
    match n with
      | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3
        ]
        rfl
      | _+20 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_30 (h_n: n < 30):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 20; exact input_bytes_sublist_eq_calc_20 h
    match n with
      | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4
        ]
        rfl
      | _+30 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_40 (h_n: n < 40):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 30; exact input_bytes_sublist_eq_calc_30 h
    match n with
      | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5
        ]
        rfl
      | _+40 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_50 (h_n: n < 50):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 40; exact input_bytes_sublist_eq_calc_40 h
    match n with
      | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7
        ]
        rfl
      | _+50 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_60 (h_n: n < 60):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 50; exact input_bytes_sublist_eq_calc_50 h
    match n with
      | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8
        ]
        rfl
      | _+60 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_70 (h_n: n < 70):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 60; exact input_bytes_sublist_eq_calc_60 h
    match n with
      | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 | 68 | 69 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9
        ]
        rfl
      | _+70 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_80 (h_n: n < 80):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 70; exact input_bytes_sublist_eq_calc_70 h
    match n with
      | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10
        ]
        rfl
      | _+80 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_90 (h_n: n < 90):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 80; exact input_bytes_sublist_eq_calc_80 h
    match n with
      | 80 | 81 | 82 | 83 | 84 | 85 | 86 | 87 | 88 | 89 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10,
          unfold_input_bytes_round 11,
          unfold_input_bytes_round 12
        ]
        rfl
      | _+90 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_100 (h_n: n < 100):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 90; exact input_bytes_sublist_eq_calc_90 h
    match n with
      | 90 | 91 | 92 | 93 | 94 | 95 | 96 | 97 | 98 | 99 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10,
          unfold_input_bytes_round 11,
          unfold_input_bytes_round 12,
          unfold_input_bytes_round 13
        ]
        rfl
      | _+100 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_110 (h_n: n < 110):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 100; exact input_bytes_sublist_eq_calc_100 h
    match n with
      | 100 | 101 | 102 | 103 | 104 | 105 | 106 | 107 | 108 | 109 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10,
          unfold_input_bytes_round 11,
          unfold_input_bytes_round 12,
          unfold_input_bytes_round 13,
          unfold_input_bytes_round 14
        ]
        rfl
      | _+110 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_120 (h_n: n < 120):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 110; exact input_bytes_sublist_eq_calc_110 h
    match n with
      | 110 | 111 | 112 | 113 | 114 | 115 | 116 | 117 | 118 | 119 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10,
          unfold_input_bytes_round 11,
          unfold_input_bytes_round 12,
          unfold_input_bytes_round 13,
          unfold_input_bytes_round 14,
          unfold_input_bytes_round 15,
        ]
        rfl
      | _+120 => exfalso; omega

  lemma input_bytes_sublist_eq_calc_130 (h_n: n < 130):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 120; exact input_bytes_sublist_eq_calc_120 h
    match n with
      | 120 | 121 | 122 | 123 | 124 | 125 | 126 | 127 | 128 | 129 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10,
          unfold_input_bytes_round 11,
          unfold_input_bytes_round 12,
          unfold_input_bytes_round 13,
          unfold_input_bytes_round 14,
          unfold_input_bytes_round 15,
          unfold_input_bytes_round 16,
          unfold_input_bytes_round 17
        ]
        rfl
      | _+130 => exfalso; omega

  lemma input_bytes_sublist_eq_calc(h_n: n ≤ 136):
    input_bytes_sublist c n =
    input_bytes_sublist_calc c n
  := by
    by_cases h: n < 130; exact input_bytes_sublist_eq_calc_130 h
    match n with
      | 130 | 131 | 132 | 133 | 134 | 135 | 136 =>
        simp [input_bytes_sublist.eq_def, list_ops, ←List.map_append]
        try rewrite [
          unfold_input_bytes_round 1,
          unfold_input_bytes_round 2,
          unfold_input_bytes_round 3,
          unfold_input_bytes_round 4,
          unfold_input_bytes_round 5,
          unfold_input_bytes_round 6,
          unfold_input_bytes_round 7,
          unfold_input_bytes_round 8,
          unfold_input_bytes_round 9,
          unfold_input_bytes_round 10,
          unfold_input_bytes_round 11,
          unfold_input_bytes_round 12,
          unfold_input_bytes_round 13,
          unfold_input_bytes_round 14,
          unfold_input_bytes_round 15,
          unfold_input_bytes_round 16,
          unfold_input_bytes_round 17,
          unfold_input_bytes_round 18
        ]
        rfl
      | _+137 => exfalso; omega

  lemma input_bytes_step (h_n: n ≤ 135):
    input_bytes_sublist_calc c (n+1) =
    input_bytes_sublist_calc c n ++ [((input_bytes c ((n/8)+1)).1[n%8]'(input_bytes_len (by omega))).2]
  := by
    match n with
      |   0 |   1 |   2 |   3 |   4 |   5 |   6 |   7 |   8 |   9 => rfl
      |  10 |  11 |  12 |  13 |  14 |  15 |  16 |  17 |  18 |  19 => rfl
      |  20 |  21 |  22 |  23 |  24 |  25 |  26 |  27 |  28 |  29 => rfl
      |  30 |  31 |  32 |  33 |  34 |  35 |  36 |  37 |  38 |  39 => rfl
      |  40 |  41 |  42 |  43 |  44 |  45 |  46 |  47 |  48 |  49 => rfl
      |  50 |  51 |  52 |  53 |  54 |  55 |  56 |  57 |  58 |  59 => rfl
      |  60 |  61 |  62 |  63 |  64 |  65 |  66 |  67 |  68 |  69 => rfl
      |  70 |  71 |  72 |  73 |  74 |  75 |  76 |  77 |  78 |  79 => rfl
      |  80 |  81 |  82 |  83 |  84 |  85 |  86 |  87 |  88 |  89 => rfl
      |  90 |  91 |  92 |  93 |  94 |  95 |  96 |  97 |  98 |  99 => rfl
      | 100 | 101 | 102 | 103 | 104 | 105 | 106 | 107 | 108 | 109 => rfl
      | 110 | 111 | 112 | 113 | 114 | 115 | 116 | 117 | 118 | 119 => rfl
      | 120 | 121 | 122 | 123 | 124 | 125 | 126 | 127 | 128 | 129 => rfl
      | 130 | 131 | 132 | 133 | 134 | 135 => rfl
      | _+136 => exfalso; omega

  def bitvec_to_zmod (P: ℕ) (b: BitVec K): ZMod P := ↑(b.toNat)

  lemma input_bytes_length:
    (input_bytes c round).1.length = 8
  := by
    simp [input_bytes.eq_def, keccak_constants, Transform.split_expr, Split.expr_res, word_parts_known]

  lemma input_bytes_value_range
    {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c)
    (h_idx: idx < 8) (round: Finset.Icc 1 24) (h_P: P ≥ 256):
    (input_bytes c round).1[idx].2.val < 256
  := by
    have h_input_bytes := Proofs.input_bytes_of_meets_constraints h_meets_constraints round round.2
    simp [
      input_bytes.eq_def, keccak_constants, Transform.split_expr, packed_parts.eq_def,
      Split.expr.eq_def, Split.constraint.eq_def, Split.expr_res.eq_def, word_parts_known
    ] at h_input_bytes
    simp [
      input_bytes.eq_def, keccak_constants, Transform.split_expr, Split.expr_res.eq_def
    ]
    by_cases idx = 0
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.1 h_P; simp_all
    by_cases idx = 1
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.1 h_P; simp_all
    by_cases idx = 2
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.2.1 h_P; simp_all
    by_cases idx = 3
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.2.2.1 h_P; simp_all
    by_cases idx = 4
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 5
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 6
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.2.2.2.2.2.1 h_P; simp_all
    by_cases idx = 7
    . convert Lookups.PackTable.apply_transform_table_output_range _ _ h_input_bytes.2.2.2.2.2.2.2.2 h_P; simp_all
    omega

  def input_rlc_induction (c: ValidCircuit P P_Prime) (n: ℕ): Prop := (
    (∀ idx: ℕ, idx ≤ n → ¬padding c idx) ∧
    input_rlc c n = ComposeRlc.expr (input_bytes_sublist c (n+1)).reverse (c.get_challenge 1 0)
  ) ∨
  (
    ∃ length: ℕ, (
      (∀ idx: ℕ, idx < length → ¬padding c idx) ∧
      (∀ idx: ℕ, idx ≥ length → idx ≤ n → padding c idx) ∧
      length ≤ n ∧
      input_rlc c n = ComposeRlc.expr (input_bytes_sublist c length).reverse (c.get_challenge 1 0)
    )
  )

  lemma input_rlc_zero {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c):
    input_rlc_induction c 0
  := by
    unfold input_rlc_induction
    have h_fixed := fixed_of_meets_constraints h_meets_constraints
    have h_initial_data_rlc := Proofs.initial_data_rlc_of_meets_constraints h_meets_constraints ⟨1, by apply Finset.mem_Icc.mpr; omega⟩
    simp [
      initial_data_rlc.eq_def, start_new_hash.eq_def, ValidCircuit.get_fixed,
      h_fixed, fixed_func, fixed_func_col_1, keccak_constants
    ] at h_initial_data_rlc
    have h_intermediate_data_rlc := Proofs.intermediate_data_rlc_of_meets_constraints h_meets_constraints ⟨1, by apply Finset.mem_Icc.mpr; omega⟩
    unfold intermediate_data_rlc at h_intermediate_data_rlc
    specialize h_intermediate_data_rlc 0
    simp [keccak_constants] at h_intermediate_data_rlc
    have h_one_lt_P: 1 < P := P_Prime.one_lt
    by_cases h_padding: padding c 0
    . simp [h_padding]
      simp [input_rlc.eq_def, keccak_constants]
      simp [padding.eq_def] at h_padding
      have h_padding : is_paddings c 1 0 = 1 := by
        apply (ZMod.val_eq_one h_one_lt_P (is_paddings c 1 0)).mp
        exact h_padding
      have h_one_neq_zero: (1: ZMod P) ≠ (0: ZMod P) := by
        symm
        simp [zmod_not_zero_eq_one, P_Prime]
      simp [h_padding, h_one_neq_zero] at h_intermediate_data_rlc
      simp_all [ComposeRlc.expr, input_bytes_sublist.eq_def, list_ops]
    . simp [h_padding]
      simp [input_rlc.eq_def, keccak_constants]
      simp [padding.eq_def] at h_padding
      have h_is_padding_boolean := Proofs.is_padding_boolean_of_meets_constraints h_meets_constraints 1 (by trivial) 0
      unfold is_padding_boolean at h_is_padding_boolean
      have h_padding : is_paddings c 1 0 = 0 := by
        by_cases h_contr: is_paddings c 1 0 = 0
        . exact h_contr
        . simp_all
          have : Fact (1 < P) := by constructor; assumption
          rewrite [ZMod.val_one] at h_padding
          simp_all
      simp_all [zmod_not_zero_eq_one, ComposeRlc.expr]
      have h_length: 0 < (input_bytes c 1).1.length := by simp [input_bytes_length]
      simp [
        input_bytes_sublist.eq_def, list_ops, input_bytes.eq_def, keccak_constants,
        Transform.split_expr, Split.expr_res.eq_def, word_parts_known
      ]

  lemma compose_rlc_step (challenge: ZMod P):
    ComposeRlc.expr list challenge * challenge + x =
    ComposeRlc.expr (x :: list) challenge
  := by
    unfold ComposeRlc.expr
    simp
    have : (List.foldl (fun x expr ↦ (x.1 + expr * x.2, x.2 * challenge)) (x, challenge) list) = (
      (List.foldl (fun x expr ↦ (x.1 + expr * x.2, x.2 * challenge)) (0, 1) list).1 * challenge + x,
      (List.foldl (fun x expr ↦ (x.1 + expr * x.2, x.2 * challenge)) (0, 1) list).2 * challenge
    ) := by
      rewrite [show list = list.reverse.reverse by simp]
      induction list.reverse with
        | nil => simp
        | cons head tail h_tail =>
          have ⟨h_tail_1, h_tail_2⟩ := Prod.mk_inj.mp h_tail
          clear h_tail
          simp_all
          clear h_tail_1 h_tail_2
          simp [add_mul, add_assoc, add_comm, mul_assoc]
    rewrite [this]
    simp

  lemma padding_next_one_of_padding_one {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_padding: padding c n)
    (h_n: n ≤ 134)
    (h_P: 2 < P):
    padding c (n+1)
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have : Fact (1 < P) := by constructor; exact P_Prime.one_lt
    have h_is_padding_boolean := Proofs.is_padding_boolean_of_meets_constraints h_meets_constraints
    simp [padding] at h_padding
    simp [padding]
    unfold is_padding_boolean at h_is_padding_boolean
    specialize h_is_padding_boolean ((n+1)/8+1) (by omega) (↑n+1)
    have h_is_padding_step := Proofs.padding_step_boolean_of_meets_constraints h_meets_constraints
    unfold padding_step_boolean is_first_padding is_padding_prev at h_is_padding_step
    specialize h_is_padding_step ⟨((n+1)/8+1), (by apply Finset.mem_Icc.mpr; omega)⟩ (↑n+1)
    cases h_is_padding_step with
      | inl h_is_padding_step =>
        apply sub_eq_zero.mp at h_is_padding_step
        by_cases h: (↑n+1: Fin 8) = 0
        . simp_all
          have : (↑n: Fin 8) = 7 := by omega
          simp_all
          rewrite [Nat.add_div (by trivial), if_pos]
          . simp
            convert h_padding
          . simp
            rewrite [show n%8 = ((n: Fin 8): ℕ) by rfl, this]
            rfl
        . simp_all [Nat.add_div]
          by_cases h_contr: 7 ≤ n%8
          . exfalso
            have : (n: Fin 8) = 7 := by
              rewrite [show n%8 = ((n: Fin 8): ℕ) by rfl] at h_contr
              omega
            omega
          . rewrite [if_neg h_contr]
            simp_all
      | inr h_is_padding_step =>
        simp_all
        replace h_is_padding_step := add_eq_of_eq_sub h_is_padding_step.symm
        cases h_is_padding_boolean with
          | inl h_contr =>
            exfalso
            rewrite [h_contr] at h_is_padding_step
            clear h_contr
            have h_is_padding_boolean := Proofs.is_padding_boolean_of_meets_constraints h_meets_constraints
            unfold is_padding_boolean at h_is_padding_boolean
            by_cases (n: Fin 8)+1 = 0
            . simp_all
              specialize h_is_padding_boolean ((n+1)/8) (by omega) (-1)
              cases h_is_padding_boolean with
                | inl h_zero => simp_all
                | inr h_one =>
                  simp_all
                  have h_contr: ((1: ZMod P)+1).val = ((1: ZMod P).val + (1: ZMod P).val)%P := by
                    apply ZMod.val_add
                  rewrite [h_is_padding_step] at h_contr
                  simp_all [ZMod.val_one, Nat.mod_eq_of_lt h_P]
            . simp_all
              specialize h_is_padding_boolean ((n+1)/8+1) (by omega) (n: Fin 8)
              cases h_is_padding_boolean with
                | inl h_zero => simp_all
                | inr h_one =>
                  simp_all
                  have h_contr: ((1: ZMod P)+1).val = ((1: ZMod P).val + (1: ZMod P).val)%P := by
                    apply ZMod.val_add
                  rewrite [h_is_padding_step] at h_contr
                  simp_all [ZMod.val_one, Nat.mod_eq_of_lt h_P]
          | inr h =>
            rw [h, ZMod.val_one]

  lemma input_rlc_step {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_step: input_rlc_induction c n)
    (h_n: n < 135)
    (h_is_final: ∀ row < 300, is_final c row = 0)
    (h_P: 2 < P)
  :
    input_rlc_induction c (n+1)
  := by
    unfold input_rlc_induction
    unfold input_rlc_induction at h_step
    have h_fixed := fixed_of_meets_constraints h_meets_constraints
    have h_initial_data_rlc := Proofs.initial_data_rlc_of_meets_constraints h_meets_constraints
    unfold initial_data_rlc at h_initial_data_rlc
    simp [keccak_constants, start_new_hash] at h_initial_data_rlc
    have h_intermediate_data_rlc := Proofs.intermediate_data_rlc_of_meets_constraints h_meets_constraints ⟨(n+1)/8+1, by apply Finset.mem_Icc.mpr; omega⟩
    unfold intermediate_data_rlc at h_intermediate_data_rlc
    simp [keccak_constants] at h_intermediate_data_rlc
    have h_input_rlc_n_plus_1: data_rlc c (12 * ((n + 1) / 8 + 1) + 7 - (n + 1) % 8) = input_rlc c (n+1) := by
      simp [input_rlc, keccak_constants]
    have h_input_rlc_n : data_rlc c (12 * ((n + 1) / 8 + 1) + 8 - (n + 1) % 8) = input_rlc c n := by
      simp [input_rlc, keccak_constants]
      by_cases h_mod: (n%8) = 7
      . rewrite [Nat.add_mod, h_mod]
        norm_num
        rewrite [Nat.add_div (by trivial), h_mod]
        simp
        specialize h_initial_data_rlc (n/8+1+1) (by omega) (by omega)
        simp [ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1] at h_initial_data_rlc
        replace h_initial_data_rlc := h_initial_data_rlc.2
        rewrite [if_pos (by omega)] at h_initial_data_rlc
        simp [zmod_not_zero_eq_one, P_Prime] at h_initial_data_rlc
        specialize h_is_final (12*(n/8+1)) (by omega)
        rewrite [h_is_final] at h_initial_data_rlc
        simp [zmod_not_zero_eq_one, P_Prime] at h_initial_data_rlc
        exact h_initial_data_rlc
      . rewrite [Nat.add_div (by trivial), if_neg (by omega)]
        simp
        have : 8-(n+1)%8 = 7 - n%8 := by omega
        rewrite [Nat.add_sub_assoc (by omega), Nat.add_sub_assoc (by omega)]
        rw [this]
    cases h_step with
      | inl h_step =>
        by_cases h_padding: padding c (n+1)
        . right
          use (n+1)
          split_ands
          . intro idx h_idx
            apply h_step.1
            omega
          . intro idx h_idx_low h_idx_high
            have : idx = n+1 := by omega
            simp_all
          . rfl
          . rewrite [←h_step.2]
            unfold padding at h_padding
            simp_all
            specialize h_intermediate_data_rlc (↑n+1)
            cases h_intermediate_data_rlc with
              | inl h_contr => rewrite [h_contr.1] at h_padding; exfalso; simp_all
              | inr h_intermediate_data_rlc =>
                rewrite [←h_step.2]
                simp [input_rlc.eq_def, keccak_constants]
                rewrite [Fin.val_add] at h_intermediate_data_rlc
                simp at h_intermediate_data_rlc
                rewrite [h_intermediate_data_rlc.2, Nat.add_div (by trivial), Nat.add_mod]
                simp only [Nat.reduceDiv, add_zero, Nat.one_mod, Nat.reduceLeDiff]
                by_cases h_mod: n%8 < 7
                . rewrite [if_neg (by omega)]
                  rewrite [Nat.mod_eq_of_lt (a := n%8+1) (by omega)]
                  simp
                . have h_mod : n%8=7 := by omega
                  simp only [h_mod]
                  simp
                  have h_n_plus_one_div: (n+1)/8 = n/8+1 := by omega
                  have h_n_plus_one_mod: (n+1)%8 = 0 := by omega
                  simp_all
                  specialize h_initial_data_rlc (n/8 + 1 + 1)
                  have : 1 ≤ n / 8 + 1 + 1 := by omega
                  have : n / 8 + 1 + 1 ≤ 17 := by omega
                  simp_all [ValidCircuit.get_fixed, h_fixed, fixed_func, fixed_func_col_1]
                  have : 1 ≤ 12 * (n/8+1) := by omega
                  have : 12*(n/8+1) ≤ 311 := by omega
                  have : 12*(n/8+1) < 300 := by omega
                  simp_all [zmod_not_zero_eq_one, h_is_final]
        . left
          split_ands
          . intro idx h_idx
            by_cases h_idx': idx ≤ n
            . simp_all
            . have : idx = n+1 := by omega
              simp_all
          . rewrite [input_bytes_sublist_eq_calc (by omega), input_bytes_step (by omega)]
            specialize h_intermediate_data_rlc (n+1)
            simp [Fin.val_add, h_input_rlc_n_plus_1] at h_intermediate_data_rlc
            rewrite [h_input_rlc_n] at h_intermediate_data_rlc
            cases h_intermediate_data_rlc with
              | inl h_intermediate_data_rlc =>
                have : (n+1)%8 = @Fin.val 8 (↑n+1) := by simp [Fin.val_add]
                simp [←this] at h_intermediate_data_rlc
                rewrite [h_intermediate_data_rlc.2]
                rewrite [h_step.2]
                rewrite [List.reverse_append, List.reverse_singleton, List.singleton_append]
                rw [compose_rlc_step, input_bytes_sublist_eq_calc (by omega)]
              | inr h_intermediate_data_rlc =>
                simp [padding.eq_def] at h_padding
                rewrite [h_intermediate_data_rlc.1] at h_padding
                have : Fact (1<P) := by constructor; exact P_Prime.one_lt
                rewrite [ZMod.val_one] at h_padding
                aesop
      | inr h_step =>
        obtain ⟨length, ⟨h_padding_false,h_padding_true,h_length, h_rlc⟩⟩ := h_step
        right
        use length
        split_ands
        . exact h_padding_false
        . intro idx h_idx_length h_idx_n
          by_cases h_idx: idx = n+1
          . rewrite [h_idx]
            apply padding_next_one_of_padding_one
            . exact h_meets_constraints
            . exact h_padding_true n (by omega) (by omega)
            . omega
            . exact h_P
          . exact h_padding_true idx (by omega) (by omega)
        . omega
        . rewrite [←h_rlc]
          specialize h_intermediate_data_rlc (n+1)
          simp [Fin.val_add] at h_intermediate_data_rlc
          rewrite [h_input_rlc_n] at h_intermediate_data_rlc
          rewrite [h_input_rlc_n_plus_1] at h_intermediate_data_rlc
          cases h_intermediate_data_rlc with
            | inl h_intermediate_data_rlc =>
              exfalso
              by_cases h_padding : padding c (n+1)
              . simp [padding, h_intermediate_data_rlc.1] at h_padding
              . have := h_padding_true n (by omega) (by omega)
                have := padding_next_one_of_padding_one h_meets_constraints this (by omega) (by omega)
                contradiction
            | inr h_intermediate_data_rlc =>
              exact h_intermediate_data_rlc.2

  lemma input_rlc_of_meets_constraints {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c)
    (h_n: n ≤ 135)
    (h_is_final: ∀ row < 300, is_final c row = 0)
    (h_P: 2 < P):
    input_rlc_induction c n
  := by
    induction n with
      | zero => exact input_rlc_zero h_meets_constraints
      | succ n h_step =>
        specialize h_step (by omega)
        apply input_rlc_step
        . exact h_meets_constraints
        . exact h_step
        . omega
        . exact h_is_final
        . exact h_P

  lemma length_of_all_padding_false {c: ValidCircuit P P_Prime}
    (h_meets_constraints: meets_constraints c) (h_padding: ∀ n ≤ 135, ¬padding c n) (h_is_final: ∀ row < 300, ¬is_final c row = 1) (h_P: 136 < P):
    (length c 300).val = 136
  := by
    have h_fixed := fixed_of_meets_constraints h_meets_constraints
    have h_update_length := Proofs.update_length_of_meets_constraints h_meets_constraints
    unfold update_length at h_update_length
    simp [keccak_constants, start_new_hash, ValidCircuit.get_fixed, h_fixed, fixed_func] at h_update_length
    simp [padding] at h_padding
    have : Fact (1 < P) := by constructor; exact P_Prime.one_lt
    have h_padding: ∀ n ≤ 135, (is_paddings c (n/8 + 1) ↑n).val = 0 := by
      intro n h_n
      have h_padding_boolean := Proofs.is_padding_boolean_of_meets_constraints h_meets_constraints (n/8+1) (by omega) n
      unfold is_padding_boolean at h_padding_boolean
      specialize h_padding n h_n
      cases h_padding_boolean with
        | inl h => simp_all
        | inr h => rewrite [h, ZMod.val_one] at h_padding; simp_all
    have : (length c 12).val = 8 := by
      specialize h_update_length 1 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 0 (by trivial)
      have := h_padding 1 (by trivial)
      have := h_padding 2 (by trivial)
      have := h_padding 3 (by trivial)
      have := h_padding 4 (by trivial)
      have := h_padding 5 (by trivial)
      have := h_padding 6 (by trivial)
      have := h_padding 7 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 24).val = 16 := by
      specialize h_update_length 2 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 8 (by trivial)
      have := h_padding 9 (by trivial)
      have := h_padding 10 (by trivial)
      have := h_padding 11 (by trivial)
      have := h_padding 12 (by trivial)
      have := h_padding 13 (by trivial)
      have := h_padding 14 (by trivial)
      have := h_padding 15 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 36).val = 24 := by
      specialize h_update_length 3 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 16 (by trivial)
      have := h_padding 17 (by trivial)
      have := h_padding 18 (by trivial)
      have := h_padding 19 (by trivial)
      have := h_padding 20 (by trivial)
      have := h_padding 21 (by trivial)
      have := h_padding 22 (by trivial)
      have := h_padding 23 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 48).val = 32 := by
      specialize h_update_length 4 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 24 (by trivial)
      have := h_padding 25 (by trivial)
      have := h_padding 26 (by trivial)
      have := h_padding 27 (by trivial)
      have := h_padding 28 (by trivial)
      have := h_padding 29 (by trivial)
      have := h_padding 30 (by trivial)
      have := h_padding 31 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 60).val = 40 := by
      specialize h_update_length 5 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 32 (by trivial)
      have := h_padding 33 (by trivial)
      have := h_padding 34 (by trivial)
      have := h_padding 35 (by trivial)
      have := h_padding 36 (by trivial)
      have := h_padding 37 (by trivial)
      have := h_padding 38 (by trivial)
      have := h_padding 39 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 72).val = 48 := by
      specialize h_update_length 6 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 40 (by trivial)
      have := h_padding 41 (by trivial)
      have := h_padding 42 (by trivial)
      have := h_padding 43 (by trivial)
      have := h_padding 44 (by trivial)
      have := h_padding 45 (by trivial)
      have := h_padding 46 (by trivial)
      have := h_padding 47 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 84).val = 56 := by
      specialize h_update_length 7 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 48 (by trivial)
      have := h_padding 49 (by trivial)
      have := h_padding 50 (by trivial)
      have := h_padding 51 (by trivial)
      have := h_padding 52 (by trivial)
      have := h_padding 53 (by trivial)
      have := h_padding 54 (by trivial)
      have := h_padding 55 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 96).val = 64 := by
      specialize h_update_length 8 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 56 (by trivial)
      have := h_padding 57 (by trivial)
      have := h_padding 58 (by trivial)
      have := h_padding 59 (by trivial)
      have := h_padding 60 (by trivial)
      have := h_padding 61 (by trivial)
      have := h_padding 62 (by trivial)
      have := h_padding 63 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 108).val = 72 := by
      specialize h_update_length 9 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 64 (by trivial)
      have := h_padding 65 (by trivial)
      have := h_padding 66 (by trivial)
      have := h_padding 67 (by trivial)
      have := h_padding 68 (by trivial)
      have := h_padding 69 (by trivial)
      have := h_padding 70 (by trivial)
      have := h_padding 71 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 120).val = 80 := by
      specialize h_update_length 10 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 72 (by trivial)
      have := h_padding 73 (by trivial)
      have := h_padding 74 (by trivial)
      have := h_padding 75 (by trivial)
      have := h_padding 76 (by trivial)
      have := h_padding 77 (by trivial)
      have := h_padding 78 (by trivial)
      have := h_padding 79 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 132).val = 88 := by
      specialize h_update_length 11 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 80 (by trivial)
      have := h_padding 81 (by trivial)
      have := h_padding 82 (by trivial)
      have := h_padding 83 (by trivial)
      have := h_padding 84 (by trivial)
      have := h_padding 85 (by trivial)
      have := h_padding 86 (by trivial)
      have := h_padding 87 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 144).val = 96 := by
      specialize h_update_length 12 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 88 (by trivial)
      have := h_padding 89 (by trivial)
      have := h_padding 90 (by trivial)
      have := h_padding 91 (by trivial)
      have := h_padding 92 (by trivial)
      have := h_padding 93 (by trivial)
      have := h_padding 94 (by trivial)
      have := h_padding 95 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 156).val = 104 := by
      specialize h_update_length 13 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 96 (by trivial)
      have := h_padding 97 (by trivial)
      have := h_padding 98 (by trivial)
      have := h_padding 99 (by trivial)
      have := h_padding 100 (by trivial)
      have := h_padding 101 (by trivial)
      have := h_padding 102 (by trivial)
      have := h_padding 103 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 168).val = 112 := by
      specialize h_update_length 14 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 104 (by trivial)
      have := h_padding 105 (by trivial)
      have := h_padding 106 (by trivial)
      have := h_padding 107 (by trivial)
      have := h_padding 108 (by trivial)
      have := h_padding 109 (by trivial)
      have := h_padding 110 (by trivial)
      have := h_padding 111 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 180).val = 120 := by
      specialize h_update_length 15 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 112 (by trivial)
      have := h_padding 113 (by trivial)
      have := h_padding 114 (by trivial)
      have := h_padding 115 (by trivial)
      have := h_padding 116 (by trivial)
      have := h_padding 117 (by trivial)
      have := h_padding 118 (by trivial)
      have := h_padding 119 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 192).val = 128 := by
      specialize h_update_length 16 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 120 (by trivial)
      have := h_padding 121 (by trivial)
      have := h_padding 122 (by trivial)
      have := h_padding 123 (by trivial)
      have := h_padding 124 (by trivial)
      have := h_padding 125 (by trivial)
      have := h_padding 126 (by trivial)
      have := h_padding 127 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have : (length c 204).val = 136 := by
      specialize h_update_length 17 (by omega) (by omega)
      simp [h_is_final, fixed_func_col_1] at h_update_length
      have := h_padding 128 (by trivial)
      have := h_padding 129 (by trivial)
      have := h_padding 130 (by trivial)
      have := h_padding 131 (by trivial)
      have := h_padding 132 (by trivial)
      have := h_padding 133 (by trivial)
      have := h_padding 134 (by trivial)
      have := h_padding 135 (by trivial)
      simp_all [ZMod.val_add, ZMod.val_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    have h_length_equality := Proofs.length_equality_check_of_meets_constraints h_meets_constraints
    unfold length_equality_check at h_length_equality
    simp [keccak_constants] at h_length_equality
    have : (length c 216).val = 136 := by
      specialize h_length_equality 18 (by trivial) (by trivial)
      simp_all
    have : (length c 228).val = 136 := by
      specialize h_length_equality 19 (by trivial) (by trivial)
      simp_all
    have : (length c 240).val = 136 := by
      specialize h_length_equality 20 (by trivial) (by trivial)
      simp_all
    have : (length c 252).val = 136 := by
      specialize h_length_equality 21 (by trivial) (by trivial)
      simp_all
    have : (length c 264).val = 136 := by
      specialize h_length_equality 22 (by trivial) (by trivial)
      simp_all
    have : (length c 276).val = 136 := by
      specialize h_length_equality 23 (by trivial) (by trivial)
      simp_all
    have : (length c 288).val = 136 := by
      specialize h_length_equality 24 (by trivial) (by trivial)
      simp_all
    specialize h_length_equality 25 (by trivial) (by trivial)
    simp_all

end Keccak.Soundness

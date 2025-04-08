import Examples.Scroll.Keccak.Soundness.BitInvert
import Examples.Scroll.Keccak.Soundness.RhoRange.All
import Examples.Scroll.Keccak.Soundness.RhoState

namespace Keccak.Soundness
  lemma state_0_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 399).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 398).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 397).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 396).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 347).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 346).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 345).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 344).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 343).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 342).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 341).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 340).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 339).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 338).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 337).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 336).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_0_0 c round
  := by
    unfold rho_s_0_0
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_336 := (cell_336_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_337 := (cell_337_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_338 := (cell_338_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_339 := (cell_339_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_340 := (cell_340_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_341 := (cell_341_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_342 := (cell_342_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_343 := (cell_343_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_344 := (cell_344_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_345 := (cell_345_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_346 := (cell_346_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_347 := (cell_347_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_396 := (cell_396_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_397 := (cell_397_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_398 := (cell_398_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_399 := (cell_399_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_336 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_337 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_337 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_338 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_338 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_339 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_339 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_340 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_340 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_341 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_341 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_342 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_342 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_343 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_343 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_344 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_344 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_345 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_345 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_346 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_346 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_347 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_347 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_396 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_396 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_397 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_397 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_398 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_398 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_399 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_399 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_0_0_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 399).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 398).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 397).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 396).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 347).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 346).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 345).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 344).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 343).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 342).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 341).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 340).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 339).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 338).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 337).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 336).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_0_0 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_336_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_337_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_338_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_339_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_340_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_341_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_342_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_343_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_344_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_345_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_346_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_347_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_396_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_397_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_398_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_399_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_0_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 651).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 650).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 649).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 648).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 599).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 598).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 597).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 596).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 595).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 594).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 593).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 592).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 591).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 590).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 589).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 588).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_0_1 c round
  := by
    unfold rho_s_0_1
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_588_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_589_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_590_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_591_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_592_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_593_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_594_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_595_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_596_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_597_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_598_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_599_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_648_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_649_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_650_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_651_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_0_1_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 651).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 650).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 649).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 648).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 599).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 598).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 597).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 596).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 595).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 594).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 593).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 592).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 591).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 590).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 589).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 588).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_0_1 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_588_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_589_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_590_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_591_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_592_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_593_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_594_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_595_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_596_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_597_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_598_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_599_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_648_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_649_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_650_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_651_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_0_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 487).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 486).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 485).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 484).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 483).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 482).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 481).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 480).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 431).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 430).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 429).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 428).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 427).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 426).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 425).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 424).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_0_2 c round
  := by
    unfold rho_s_0_2
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_424_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_425_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_426_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_427_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_428_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_429_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_430_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_431_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_480_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_481_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_482_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_483_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_484_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_485_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_486_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_487_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_0_2_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 487).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 486).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 485).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 484).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 483).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 482).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 481).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 480).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 431).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 430).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 429).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 428).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 427).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 426).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 425).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 424).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_0_2 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_424_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_425_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_426_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_427_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_428_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_429_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_430_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_431_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_480_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_481_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_482_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_483_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_484_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_485_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_486_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_487_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_0_3 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 739).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 738).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 737).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 736).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 735).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 734).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 733).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 732).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 683).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 682).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 681).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 680).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 679).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 678).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 677).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 676).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_0_3 c round
  := by
    unfold rho_s_0_3
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_676_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_677_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_678_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_679_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_680_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_681_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_682_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_683_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_732_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_733_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_734_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_735_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_736_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_737_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_738_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_739_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_0_3_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 739).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 738).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 737).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 736).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 735).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 734).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 733).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 732).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 683).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 682).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 681).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 680).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 679).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 678).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 677).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 676).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_0_3 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_676_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_677_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_678_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_679_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_680_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_681_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_682_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_683_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_732_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_733_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_734_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_735_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_736_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_737_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_738_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_739_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_0_4 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 575).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 574).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 573).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 572).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 571).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 570).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 569).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 568).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 567).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 566).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 565).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 564).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 515).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 514).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 513).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 512).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_0_4 c round
  := by
    unfold rho_s_0_4
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_512_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_513_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_514_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_515_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_564_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_565_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_566_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_567_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_568_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_569_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_570_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_571_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_572_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_573_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_574_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_575_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_0_4_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 575).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 574).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 573).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 572).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 571).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 570).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 569).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 568).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 567).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 566).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 565).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 564).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 515).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 514).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 513).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 512).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_0_4 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_512_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_513_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_514_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_515_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_564_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_565_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_566_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_567_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_568_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_569_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_570_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_571_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_572_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_573_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_574_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_575_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_1_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 527).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 526).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 525).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 524).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 523).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 522).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 521).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 520).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 519).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 518).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 517).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 516).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 467).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 466).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 465).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 464).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_1_0 c round
  := by
    unfold rho_s_1_0
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_464_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_465_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_466_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_467_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_516_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_517_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_518_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_519_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_520_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_521_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_522_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_523_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_524_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_525_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_526_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_527_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_1_0_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 527).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 526).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 525).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 524).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 523).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 522).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 521).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 520).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 519).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 518).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 517).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 516).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 467).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 466).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 465).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 464).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_1_0 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_464_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_465_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_466_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_467_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_516_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_517_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_518_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_519_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_520_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_521_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_522_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_523_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_524_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_525_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_526_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_527_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_1_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 411).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 410).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 409).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 408).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 359).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 358).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 357).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 356).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 355).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 354).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 353).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 352).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 351).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 350).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 349).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 348).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_1_1 c round
  := by
    unfold rho_s_1_1
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_348_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_349_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_350_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_351_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_352_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_353_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_354_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_355_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_356_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_357_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_358_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_359_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_408_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_409_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_410_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_411_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_1_1_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 411).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 410).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 409).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 408).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 359).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 358).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 357).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 356).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 355).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 354).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 353).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 352).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 351).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 350).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 349).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 348).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_1_1 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_348_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_349_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_350_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_351_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_352_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_353_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_354_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_355_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_356_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_357_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_358_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_359_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_408_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_409_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_410_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_411_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_1_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 663).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 662).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 661).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 660).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 611).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 610).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 609).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 608).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 607).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 606).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 605).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 604).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 603).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 602).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 601).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 600).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_1_2 c round
  := by
    unfold rho_s_1_2
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_600_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_601_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_602_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_603_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_604_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_605_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_606_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_607_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_608_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_609_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_610_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_611_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_660_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_661_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_662_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_663_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_1_2_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 663).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 662).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 661).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 660).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 611).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 610).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 609).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 608).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 607).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 606).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 605).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 604).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 603).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 602).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 601).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 600).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_1_2 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_600_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_601_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_602_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_603_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_604_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_605_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_606_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_607_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_608_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_609_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_610_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_611_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_660_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_661_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_662_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_663_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_1_3 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 499).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 498).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 497).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 496).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 495).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 494).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 493).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 492).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 443).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 442).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 441).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 440).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 439).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 438).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 437).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 436).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_1_3 c round
  := by
    unfold rho_s_1_3
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_436_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_437_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_438_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_439_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_440_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_441_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_442_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_443_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_492_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_493_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_494_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_495_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_496_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_497_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_498_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_499_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_1_3_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 499).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 498).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 497).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 496).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 495).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 494).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 493).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 492).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 443).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 442).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 441).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 440).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 439).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 438).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 437).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 436).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_1_3 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_436_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_437_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_438_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_439_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_440_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_441_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_442_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_443_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_492_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_493_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_494_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_495_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_496_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_497_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_498_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_499_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_1_4 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 751).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 750).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 749).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 748).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 747).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 746).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 745).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 744).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 695).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 694).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 693).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 692).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 691).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 690).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 689).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 688).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_1_4 c round
  := by
    unfold rho_s_1_4
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_688_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_689_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_690_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_691_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_692_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_693_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_694_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_695_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_744_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_745_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_746_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_747_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_748_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_749_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_750_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_751_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_1_4_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 751).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 750).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 749).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 748).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 747).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 746).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 745).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 744).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 695).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 694).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 693).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 692).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 691).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 690).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 689).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 688).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_1_4 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_688_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_689_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_690_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_691_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_692_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_693_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_694_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_695_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_744_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_745_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_746_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_747_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_748_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_749_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_750_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_751_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_2_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 703).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 702).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 701).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 700).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 699).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 698).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 697).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 696).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 647).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 646).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 645).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 644).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 643).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 642).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 641).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 640).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_2_0 c round
  := by
    unfold rho_s_2_0
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_640_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_641_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_642_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_643_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_644_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_645_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_646_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_647_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_696_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_697_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_698_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_699_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_700_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_701_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_702_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_703_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_2_0_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 703).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 702).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 701).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 700).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 699).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 698).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 697).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 696).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 647).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 646).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 645).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 644).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 643).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 642).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 641).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 640).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_2_0 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_640_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_641_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_642_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_643_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_644_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_645_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_646_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_647_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_696_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_697_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_698_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_699_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_700_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_701_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_702_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_703_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_2_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 539).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 538).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 537).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 536).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 535).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 534).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 533).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 532).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 531).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 530).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 529).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 528).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 479).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 478).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 477).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 476).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_2_1 c round
  := by
    unfold rho_s_2_1
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_476_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_477_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_478_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_479_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_528_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_529_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_530_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_531_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_532_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_533_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_534_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_535_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_536_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_537_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_538_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_15 := (cell_539_normalize_4_input_range h_meets_constraints h_round (by omega))
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_2_1_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 539).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 538).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 537).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 536).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 535).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 534).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 533).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 532).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 531).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 530).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 529).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 528).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 479).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 478).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 477).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 476).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_2_1 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_476_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_477_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_478_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_479_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_528_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_529_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_530_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_531_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_532_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_533_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_534_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_535_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_536_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_537_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_538_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_539_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_2_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 423).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 422).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 421).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 420).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 371).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 370).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 369).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 368).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 367).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 366).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 365).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 364).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 363).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 362).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 361).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 360).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_2_2 c round
  := by
    unfold rho_s_2_2
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_360_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_361_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_362_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_363_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_364_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_365_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_366_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_367_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_368_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_369_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_370_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_371_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_420_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_421_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_422_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_423_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_2_2_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 423).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 422).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 421).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 420).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 371).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 370).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 369).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 368).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 367).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 366).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 365).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 364).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 363).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 362).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 361).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 360).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_2_2 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_360_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_361_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_362_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_363_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_364_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_365_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_366_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_367_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_368_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_369_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_370_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_371_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_420_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_421_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_422_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_423_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_2_3 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 675).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 674).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 673).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 672).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 623).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 622).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 621).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 620).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 619).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 618).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 617).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 616).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 615).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 614).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 613).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 612).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_2_3 c round
  := by
    unfold rho_s_2_3
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_612_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_613_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_614_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_615_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_616_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_617_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_618_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_619_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_620_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_621_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_622_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_623_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_672_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_673_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_674_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_675_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_2_3_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 675).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 674).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 673).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 672).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 623).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 622).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 621).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 620).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 619).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 618).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 617).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 616).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 615).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 614).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 613).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 612).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_2_3 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_612_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_613_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_614_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_615_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_616_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_617_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_618_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_619_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_620_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_621_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_622_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_623_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_672_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_673_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_674_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_675_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_2_4 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 511).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 510).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 509).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 508).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 507).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 506).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 505).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 504).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 455).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 454).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 453).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 452).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 451).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 450).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 449).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 448).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_2_4 c round
  := by
    unfold rho_s_2_4
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_448_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_449_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_450_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_451_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_452_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_453_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_454_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_455_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_504_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_505_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_506_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_507_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_508_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_509_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_510_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_511_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_2_4_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 511).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 510).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 509).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 508).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 507).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 506).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 505).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 504).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 455).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 454).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 453).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 452).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 451).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 450).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 449).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 448).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_2_4 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_448_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_449_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_450_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_451_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_452_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_453_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_454_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_455_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_504_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_505_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_506_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_507_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_508_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_509_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_510_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_511_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_3_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 463).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 462).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 461).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 460).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 459).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 458).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 457).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 456).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 407).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 406).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 405).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 404).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 403).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 402).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 401).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 400).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_3_0 c round
  := by
    unfold rho_s_3_0
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_400_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_401_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_402_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_403_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_404_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_405_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_406_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_407_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_456_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_457_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_458_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_459_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_460_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_461_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_462_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_463_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_3_0_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 463).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 462).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 461).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 460).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 459).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 458).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 457).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 456).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 407).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 406).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 405).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 404).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 403).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 402).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 401).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 400).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_3_0 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_400_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_401_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_402_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_403_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_404_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_405_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_406_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_407_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_456_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_457_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_458_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_459_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_460_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_461_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_462_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_463_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_3_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 715).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 714).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 713).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 712).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 711).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 710).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 709).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 708).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 659).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 658).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 657).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 656).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 655).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 654).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 653).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 652).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_3_1 c round
  := by
    unfold rho_s_3_1
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_652_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_653_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_654_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_655_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_656_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_657_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_658_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_659_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_708_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_709_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_710_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_711_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_712_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_713_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_714_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_715_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_3_1_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 715).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 714).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 713).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 712).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 711).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 710).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 709).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 708).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 659).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 658).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 657).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 656).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 655).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 654).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 653).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 652).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_3_1 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_652_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_653_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_654_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_655_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_656_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_657_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_658_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_659_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_708_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_709_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_710_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_711_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_712_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_713_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_714_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_715_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_3_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 551).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 550).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 549).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 548).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 547).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 546).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 545).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 544).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 543).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 542).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 541).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 540).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 491).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 490).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 489).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 488).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_3_2 c round
  := by
    unfold rho_s_3_2
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_488_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_489_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_490_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_491_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_540_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_541_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_542_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_543_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_544_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_545_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_546_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_547_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_548_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_549_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_550_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_551_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_3_2_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 551).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 550).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 549).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 548).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 547).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 546).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 545).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 544).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 543).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 542).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 541).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 540).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 491).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 490).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 489).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 488).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_3_2 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_488_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_489_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_490_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_491_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_540_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_541_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_542_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_543_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_544_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_545_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_546_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_547_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_548_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_549_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_550_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_551_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_3_3 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 435).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 434).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 433).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 432).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 383).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 382).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 381).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 380).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 379).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 378).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 377).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 376).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 375).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 374).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 373).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 372).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_3_3 c round
  := by
    unfold rho_s_3_3
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_372_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_373_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_374_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_375_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_376_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_377_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_378_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_379_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_380_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_381_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_382_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_383_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_432_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_433_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_434_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_435_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_3_3_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 435).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 434).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 433).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 432).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 383).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 382).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 381).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 380).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 379).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 378).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 377).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 376).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 375).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 374).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 373).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 372).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_3_3 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_372_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_373_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_374_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_375_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_376_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_377_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_378_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_379_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_380_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_381_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_382_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_383_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_432_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_433_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_434_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_435_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_3_4 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 687).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 686).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 685).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 684).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 635).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 634).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 633).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 632).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 631).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 630).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 629).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 628).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 627).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 626).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 625).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 624).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_3_4 c round
  := by
    unfold rho_s_3_4
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_624_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_625_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_626_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_627_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_628_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_629_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_630_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_631_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_632_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_633_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_634_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_635_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_684_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_685_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_686_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_687_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_3_4_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 687).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 686).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 685).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 684).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 635).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 634).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 633).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 632).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 631).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 630).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 629).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 628).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 627).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 626).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 625).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 624).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_3_4 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_624_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_625_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_626_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_627_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_628_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_629_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_630_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_631_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_632_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_633_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_634_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_635_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_684_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_685_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_686_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_687_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_4_0 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 639).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 638).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 637).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 636).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 587).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 586).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 585).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 584).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 583).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 582).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 581).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 580).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 579).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 578).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 577).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 576).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_4_0 c round
  := by
    unfold rho_s_4_0
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_576_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_577_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_578_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_579_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_580_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_581_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_582_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_583_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_584_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_585_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_586_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_587_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_636_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_637_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_638_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_639_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_4_0_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 639).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 638).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 637).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 636).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 587).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 586).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 585).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 584).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 583).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 582).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 581).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 580).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 579).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 578).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 577).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 576).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_4_0 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_576_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_577_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_578_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_579_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_580_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_581_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_582_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_583_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_584_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_585_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_586_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_587_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_636_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_637_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_638_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_639_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_4_1 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 475).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 474).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 473).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 472).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 471).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 470).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 469).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 468).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 419).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 418).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 417).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 416).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 415).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 414).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 413).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 412).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_4_1 c round
  := by
    unfold rho_s_4_1
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_412_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_413_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_414_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_415_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_416_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_417_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_418_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_419_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_468_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_469_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_470_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_471_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_472_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_473_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_474_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_475_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_4_1_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 475).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 474).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 473).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 472).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 471).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 470).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 469).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 468).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 419).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 418).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 417).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 416).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 415).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 414).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 413).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 412).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_4_1 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_412_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_413_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_414_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_415_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_416_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_417_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_418_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_419_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_468_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_469_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_470_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_471_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_472_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_473_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_474_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_475_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_4_2 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 727).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 726).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 725).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 724).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 723).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 722).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 721).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 720).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 671).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 670).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 669).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 668).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 667).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 666).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 665).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 664).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_4_2 c round
  := by
    unfold rho_s_4_2
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_664_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_665_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_666_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_667_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_668_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_669_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_670_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_671_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_720_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_721_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_722_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_723_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_724_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_725_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_726_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_727_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_4_2_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 727).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 726).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 725).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 724).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 723).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 722).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 721).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 720).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 671).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 670).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 669).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 668).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 667).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 666).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 665).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 664).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_4_2 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_664_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_665_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_666_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_667_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_668_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_669_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_670_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_671_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_720_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_721_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_722_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_723_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_724_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_725_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_726_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_727_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_4_3 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 563).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 562).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 561).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 560).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 559).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 558).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 557).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 556).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 555).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 554).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 553).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 552).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 503).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 502).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 501).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 500).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_4_3 c round
  := by
    unfold rho_s_4_3
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_500_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_501_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_502_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_503_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_552_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_553_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_554_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_555_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_556_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_557_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_558_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_559_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_560_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_561_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_562_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_563_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_4_3_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 563).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 562).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 561).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 560).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 559).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 558).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 557).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 556).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 555).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 554).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 553).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 552).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 503).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 502).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 501).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 500).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_4_3 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_500_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_501_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_502_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_503_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_552_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_553_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_554_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_555_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_556_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_557_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_558_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_559_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_560_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_561_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_562_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_563_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl

  lemma state_4_4 {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    (((cell_manager c round 447).val % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    (((cell_manager c round 446).val % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    (((cell_manager c round 445).val % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    (((cell_manager c round 444).val % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    (((cell_manager c round 395).val % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    (((cell_manager c round 394).val % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    (((cell_manager c round 393).val % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    (((cell_manager c round 392).val % 4096 % 324518553658426726783156020576256) <<< 96 +
    (((cell_manager c round 391).val % 4096 % 79228162514264337593543950336) <<< 84 +
    (((cell_manager c round 390).val % 4096 % 19342813113834066795298816) <<< 72 +
    (((cell_manager c round 389).val % 4096 % 4722366482869645213696) <<< 60 +
    (((cell_manager c round 388).val % 4096 % 1152921504606846976) <<< 48 +
    (((cell_manager c round 387).val % 4096 % 281474976710656) <<< 36 +
    (((cell_manager c round 386).val % 4096 % 68719476736) <<< 24 +
    (((cell_manager c round 385).val % 4096 % 16777216) <<< 12 +
      (cell_manager c round 384).val % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    rho_s_4_4 c round
  := by
    unfold rho_s_4_4
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_384_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_385_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_386_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_387_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_388_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_389_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_390_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_391_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_392_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_393_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_394_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_395_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_444_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_445_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_446_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_447_normalize_4_input_range h_meets_constraints h_round h_P)
    rw [
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_0 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_1 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_2 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_3 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_4 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_5 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_6 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_7 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_8 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_9 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_10 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_11 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_12 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_13 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_14 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (lt_of_le_of_lt h_cell_15 (by trivial)),
      Nat.mod_eq_of_lt (a := _ <<< 12 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 24 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 36 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 48 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 60 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 72 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 84 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 96 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 108 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 120 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 132 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 144 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 156 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 168 + _) (by omega),
      Nat.mod_eq_of_lt (a := _ <<< 180 + _) (by omega)
    ]

  lemma state_4_4_invert {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 8 < P):
    ((bit_invert (cell_manager c round 447).val 4 % 4096 % 6277101735386680763835789423207666416102355444464034512896) <<< 180 +
    ((bit_invert (cell_manager c round 446).val 4 % 4096 % 1532495540865888858358347027150309183618739122183602176) <<< 168 +
    ((bit_invert (cell_manager c round 445).val 4 % 4096 % 374144419156711147060143317175368453031918731001856) <<< 156 +
    ((bit_invert (cell_manager c round 444).val 4 % 4096 % 91343852333181432387730302044767688728495783936) <<< 144 +
    ((bit_invert (cell_manager c round 395).val 4 % 4096 % 22300745198530623141535718272648361505980416) <<< 132 +
    ((bit_invert (cell_manager c round 394).val 4 % 4096 % 5444517870735015415413993718908291383296) <<< 120 +
    ((bit_invert (cell_manager c round 393).val 4 % 4096 % 1329227995784915872903807060280344576) <<< 108 +
    ((bit_invert (cell_manager c round 392).val 4 % 4096 % 324518553658426726783156020576256) <<< 96 +
    ((bit_invert (cell_manager c round 391).val 4 % 4096 % 79228162514264337593543950336) <<< 84 +
    ((bit_invert (cell_manager c round 390).val 4 % 4096 % 19342813113834066795298816) <<< 72 +
    ((bit_invert (cell_manager c round 389).val 4 % 4096 % 4722366482869645213696) <<< 60 +
    ((bit_invert (cell_manager c round 388).val 4 % 4096 % 1152921504606846976) <<< 48 +
    ((bit_invert (cell_manager c round 387).val 4 % 4096 % 281474976710656) <<< 36 +
    ((bit_invert (cell_manager c round 386).val 4 % 4096 % 68719476736) <<< 24 +
    ((bit_invert (cell_manager c round 385).val 4 % 4096 % 16777216) <<< 12 +
      bit_invert (cell_manager c round 384).val 4 % 4096) %
    16777216) %
    68719476736) %
    281474976710656) %
    1152921504606846976) %
    4722366482869645213696) %
    19342813113834066795298816) %
    79228162514264337593543950336) %
    324518553658426726783156020576256) %
    1329227995784915872903807060280344576) %
    5444517870735015415413993718908291383296) %
    22300745198530623141535718272648361505980416) %
    91343852333181432387730302044767688728495783936) %
    374144419156711147060143317175368453031918731001856) %
    1532495540865888858358347027150309183618739122183602176) %
    6277101735386680763835789423207666416102355444464034512896 =
    bit_invert (rho_s_4_4 c round) 64
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have h_cell_0 := (cell_384_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_1 := (cell_385_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_2 := (cell_386_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_3 := (cell_387_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_4 := (cell_388_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_5 := (cell_389_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_6 := (cell_390_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_7 := (cell_391_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_8 := (cell_392_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_9 := (cell_393_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_10 := (cell_394_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_11 := (cell_395_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_12 := (cell_444_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_13 := (cell_445_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_14 := (cell_446_normalize_4_input_range h_meets_constraints h_round h_P)
    have h_cell_15 := (cell_447_normalize_4_input_range h_meets_constraints h_round h_P)
    simp [
      Nat.mod_eq_of_lt (bit_invert_4_lt _),
    ]
    rewrite [
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial)),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (bit_invert_lt _ _) (by trivial))
    ]
    rw [
      bit_invert_4_shift_12_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_24_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_36_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_48_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_60_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_72_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_84_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_96_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_108_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_120_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_132_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_144_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_156_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_168_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
      bit_invert_4_shift_180_add (by omega), Nat.mod_eq_of_lt (a := bit_invert _ _) (by convert bit_invert_lt _ _),
    ]
    rfl
end Keccak.Soundness

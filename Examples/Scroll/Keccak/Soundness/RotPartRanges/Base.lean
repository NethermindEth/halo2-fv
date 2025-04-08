import Examples.Scroll.Keccak.Soundness.OsRange

namespace Keccak.Soundness

  lemma cell_1606_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^198 ≤ P):
    (cell_manager c round 1606).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 0 2).val < 2^192 := by exact os_range h_meets_constraints h_round h_P
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
    ] at h_range
    have h_cell_0 := (cell_425_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_426_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_427_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_428_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_429_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_430_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_431_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_480_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_481_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_482_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_483_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_484_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_485_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_486_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_487_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1606_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1607_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1616_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1616).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 0 3).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_676_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_677_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_678_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_679_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_680_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_681_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_682_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_683_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_732_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_733_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_735_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_736_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_737_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_738_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_739_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1616_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1617_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1624_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1624).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 0 4).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_512_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_513_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_514_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_515_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_565_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_566_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_567_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_568_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_569_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_570_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_571_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_572_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_573_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_574_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_575_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1624_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1625_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1596_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1596).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 1 0).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_465_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_466_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_467_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_516_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_517_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_518_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_519_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_520_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_521_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_522_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_523_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_524_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_525_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_526_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_527_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1596_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1597_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1608_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1608).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 1 2).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_600_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_601_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_603_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_604_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_605_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_606_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_607_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_608_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_609_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_610_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_611_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_660_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_661_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_662_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_663_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1608_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1609_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1618_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1618).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 1 3).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
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
    have h_cell_11 := (cell_496_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_497_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_498_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_499_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1618_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1619_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1626_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1626).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 1 4).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_689_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_690_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_691_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_692_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_693_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_694_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_695_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_744_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_745_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_746_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_747_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_748_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_749_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_750_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_751_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1626_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1627_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1598_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1598).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 2 0).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
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
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1598_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1599_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1602_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1602).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 2 1).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_476_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_478_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_479_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_528_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_529_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_530_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_531_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_532_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_533_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_534_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_535_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_536_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_537_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_538_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_539_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1602_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1603_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1610_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1610).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 2 2).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_360_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_361_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_362_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_363_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_364_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_365_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_366_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_367_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_368_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_369_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_371_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_420_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_421_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_422_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_423_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1610_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1611_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1620_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1620).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 2 3).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_612_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_613_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_614_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_616_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_617_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_618_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_619_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_620_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_621_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_622_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_623_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_672_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_673_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_674_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_675_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1620_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1621_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1628_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1628).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 2 4).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_448_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_449_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_450_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_451_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_452_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_453_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_454_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_455_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_504_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_505_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_506_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_507_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_508_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_509_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_510_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1628_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1629_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1604_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1604).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 3 1).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_652_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_653_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_654_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_655_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_656_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_657_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_658_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_659_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_708_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_709_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_710_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_711_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_712_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_714_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_715_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1604_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1605_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1612_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1612).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 3 2).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_488_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_489_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_490_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_491_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_540_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_541_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_543_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_544_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_545_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_546_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_547_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_548_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_549_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_550_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_551_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1612_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1613_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1622_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1622).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 3 3).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_372_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_373_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_374_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_375_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_376_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_378_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_379_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_380_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_381_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_382_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_383_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_432_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_433_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_434_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_435_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1622_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1623_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1600_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1600).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 4 0).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_576_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_577_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_578_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_579_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_580_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_581_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_583_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_584_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_585_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_586_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_587_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_636_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_637_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_638_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_639_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1600_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1601_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1614_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1614).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 4 2).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_664_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_665_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_666_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_667_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_668_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_669_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_670_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_671_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_720_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_722_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_723_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_724_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_725_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_726_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_727_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1614_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1615_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1630_rot_part_base {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 2^200 ≤ P):
    (cell_manager c round 1630).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨h_s_input_parts, _⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.input_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_input_parts
    have h_range: (os c round 4 4).val < 2^192 := by exact os_range h_meets_constraints h_round (by omega)
    rewrite [←h_s_input_parts] at h_range; clear  h_s_input_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
      zmod_val_ofNat_of_lt (show 4096 < P by omega),
      fin_vals,
    ] at h_range
    have h_cell_0 := (cell_384_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_1 := (cell_385_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_2 := (cell_386_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_3 := (cell_388_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_4 := (cell_389_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_5 := (cell_390_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_6 := (cell_391_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_7 := (cell_392_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_8 := (cell_393_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_9 := (cell_394_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_10 := (cell_395_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_11 := (cell_444_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_12 := (cell_445_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_13 := (cell_446_normalize_4_input_range h_meets_constraints h_round (by omega))
    have h_cell_14 := (cell_447_normalize_4_input_range h_meets_constraints h_round (by omega))
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_15 := (cell_1630_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_16 := (cell_1631_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

end Keccak.Soundness

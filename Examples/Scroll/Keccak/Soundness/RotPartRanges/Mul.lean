import Examples.Scroll.Keccak.Soundness.PiPartsRange
import Examples.Scroll.Keccak.Soundness.RhoRange.All

namespace Keccak.Soundness

  lemma cell_1607_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1607).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps
    ] at h_s_rot_parts
    have h_range := (cell_424_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1606_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1607_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1617_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1617).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_734_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1616_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1617_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1625_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1625).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 0 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_564_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1624_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1625_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1597_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1597).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_464_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1597_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1596_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1609_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1609).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_602_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1608_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1609_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1619_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1619).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_495_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1618_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1619_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1627_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1627).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 1 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_688_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1627_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1626_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1599_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1599).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_703_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1598_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1599_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1603_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1603).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_477_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1602_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1603_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1611_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1611).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_370_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1610_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1611_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1621_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1621).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_615_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1620_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1621_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1629_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1629).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 2 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_511_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1628_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1629_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1605_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1605).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 1
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_713_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1604_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1605_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1613_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1613).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_542_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1612_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1613_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1623_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1623).val < 2^9
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 3 3
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_377_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 8 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1622_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1623_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1601_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1601).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 0
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_582_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1600_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1601_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1615_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1615).val < 2^3
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 2
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_721_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 512 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1614_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1615_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

  lemma cell_1631_rot_part_mul {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_round: round ∈ Finset.Icc 1 24) (h_P: 900315 < P):
    (cell_manager c round 1631).val < 2^6
  := by
    have : NeZero P := by constructor; exact P_Prime.ne_zero
    have ⟨_, h_s_rot_parts⟩ := Proofs.s_parts_of_meets_constraints h_meets_constraints round h_round 4 4
    simp [
      keccak_constants, target_part_sizes_known, word_parts_known,
      get_rotate_count, list_ops, SplitUniform.rot_parts.eq_def,
      rho_pi_chi_cells, s_parts_cell_offsets, pi_region_start, List.rotateLeft,
      Decode.expr.eq_def, ←mul_assoc, mul_add, zmod_pow_simps, fin_vals
    ] at h_s_rot_parts
    have h_range := (cell_387_normalize_4_input_range h_meets_constraints h_round (by omega))
    rewrite [←h_s_rot_parts] at h_range; clear  h_s_rot_parts
    simp [
      ZMod.val_add, ZMod.val_mul,
      zmod_val_ofNat_of_lt (show 64 < P by omega),
    ] at h_range
    have := (Finset.mem_Icc.mp h_round).2
    have h_cell_0 := (cell_1630_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    have h_cell_1 := (cell_1631_normalize_4_input_range (round := round) h_meets_constraints (by omega) (by omega))
    rewrite [Nat.mod_eq_of_lt] at h_range <;> omega

end Keccak.Soundness

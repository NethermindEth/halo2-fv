import Examples.Scroll.Keccak.Soundness.Sequencing.Absorb
import Examples.Scroll.Keccak.Soundness.Sequencing.Squeeze

namespace Keccak.Soundness

  def state_x_y (c: ValidCircuit P P_Prime) (i j: ℕ) : UInt64 :=
    if (i,j) ∈ (absorb_positions.map λ (i, j) => (i.val, j.val))
    then UInt64.ofBitVec (
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 79).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 78).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 77).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 76).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 75).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 74).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 73).val ++
      BitVec.ofNat 8 (cell_manager c (a_slice i j + 1) 72).val
    )
    else 0

  def state_array (c: ValidCircuit P P_Prime): Array UInt64 :=
    Array.range 25
      |>.map λ n => state_x_y c (n/5) (n%5)

  lemma output_spec_of_padding {c: ValidCircuit P P_Prime} (h_meets_constraints: meets_constraints c) (h_P: P ≥ 2^200) (h_y: y < 4) (h_is_paddings: is_paddings c 17 (-1) = 1):
    (LeanCrypto.HashFunctions.keccakF (state_array c))[y * 5]? =
    .some (UInt64.ofBitVec
    (BitVec.ofNat 8 (cell_manager c (24 - y) 1687).val ++ BitVec.ofNat 8 (cell_manager c (24 - y) 1686).val ++
                BitVec.ofNat 8 (cell_manager c (24 - y) 1685).val ++
              BitVec.ofNat 8 (cell_manager c (24 - y) 1684).val ++
            BitVec.ofNat 8 (cell_manager c (24 - y) 1683).val ++
          BitVec.ofNat 8 (cell_manager c (24 - y) 1682).val ++
        BitVec.ofNat 8 (cell_manager c (24 - y) 1681).val ++
      BitVec.ofNat 8 (cell_manager c (24 - y) 1680).val))
  := by
    have h_P': P > Normalize.mask := by unfold Normalize.mask; omega
    have h_s_0_0 := initial_s_absorb_position h_meets_constraints h_P' (show (0,0) ∈ absorb_positions by decide)
    have h_s_1_0 := initial_s_absorb_position h_meets_constraints h_P' (show (1,0) ∈ absorb_positions by decide)
    have h_s_2_0 := initial_s_absorb_position h_meets_constraints h_P' (show (2,0) ∈ absorb_positions by decide)
    have h_s_3_0 := initial_s_absorb_position h_meets_constraints h_P' (show (3,0) ∈ absorb_positions by decide)
    have h_s_4_0 := initial_s_absorb_position h_meets_constraints h_P' (show (4,0) ∈ absorb_positions by decide)
    have h_s_0_1 := initial_s_absorb_position h_meets_constraints h_P' (show (0,1) ∈ absorb_positions by decide)
    have h_s_1_1 := initial_s_absorb_position h_meets_constraints h_P' (show (1,1) ∈ absorb_positions by decide)
    have h_s_2_1 := initial_s_absorb_position h_meets_constraints h_P' (show (2,1) ∈ absorb_positions by decide)
    have h_s_3_1 := initial_s_absorb_position h_meets_constraints h_P' (show (3,1) ∈ absorb_positions by decide)
    have h_s_4_1 := initial_s_absorb_position h_meets_constraints h_P' (show (4,1) ∈ absorb_positions by decide)
    have h_s_0_2 := initial_s_absorb_position h_meets_constraints h_P' (show (0,2) ∈ absorb_positions by decide)
    have h_s_1_2 := initial_s_absorb_position h_meets_constraints h_P' (show (1,2) ∈ absorb_positions by decide)
    have h_s_2_2 := initial_s_absorb_position h_meets_constraints h_P' (show (2,2) ∈ absorb_positions by decide)
    have h_s_3_2 := initial_s_absorb_position h_meets_constraints h_P' (show (3,2) ∈ absorb_positions by decide)
    have h_s_4_2 := initial_s_absorb_position h_meets_constraints h_P' (show (4,2) ∈ absorb_positions by decide)
    have h_s_0_3 := initial_s_absorb_position h_meets_constraints h_P' (show (0,3) ∈ absorb_positions by decide)
    have h_s_1_3 := initial_s_absorb_position h_meets_constraints h_P' (show (1,3) ∈ absorb_positions by decide)
    have h_s_2_3 := initial_s_non_absorb_position h_meets_constraints (show (2,3) ∉ absorb_positions by decide)
    have h_s_3_3 := initial_s_non_absorb_position h_meets_constraints (show (3,3) ∉ absorb_positions by decide)
    have h_s_4_3 := initial_s_non_absorb_position h_meets_constraints (show (4,3) ∉ absorb_positions by decide)
    have h_s_0_4 := initial_s_non_absorb_position h_meets_constraints (show (0,4) ∉ absorb_positions by decide)
    have h_s_1_4 := initial_s_non_absorb_position h_meets_constraints (show (1,4) ∉ absorb_positions by decide)
    have h_s_2_4 := initial_s_non_absorb_position h_meets_constraints (show (2,4) ∉ absorb_positions by decide)
    have h_s_3_4 := initial_s_non_absorb_position h_meets_constraints (show (3,4) ∉ absorb_positions by decide)
    have h_s_4_4 := initial_s_non_absorb_position h_meets_constraints (show (4,4) ∉ absorb_positions by decide)
    have := squeeze_bytes_equiv (h_meets_constraints := h_meets_constraints) (state := state_array c)
      (h_y := h_y) (h_P := h_P)
      (h_s_0_0 := h_s_0_0) (h_s_0_1 := h_s_0_1) (h_s_0_2 := h_s_0_2) (h_s_0_3 := h_s_0_3) (h_s_0_4 := h_s_0_4)
      (h_s_1_0 := h_s_1_0) (h_s_1_1 := h_s_1_1) (h_s_1_2 := h_s_1_2) (h_s_1_3 := h_s_1_3) (h_s_1_4 := h_s_1_4)
      (h_s_2_0 := h_s_2_0) (h_s_2_1 := h_s_2_1) (h_s_2_2 := h_s_2_2) (h_s_2_3 := h_s_2_3) (h_s_2_4 := h_s_2_4)
      (h_s_3_0 := h_s_3_0) (h_s_3_1 := h_s_3_1) (h_s_3_2 := h_s_3_2) (h_s_3_3 := h_s_3_3) (h_s_3_4 := h_s_3_4)
      (h_s_4_0 := h_s_4_0) (h_s_4_1 := h_s_4_1) (h_s_4_2 := h_s_4_2) (h_s_4_3 := h_s_4_3) (h_s_4_4 := h_s_4_4)
      (h_is_paddings := h_is_paddings) (h_state := by {
        simp [state_array.eq_def, array_range_25, state_x_y, fin_vals, absorb_positions]
      })
    symm at this
    apply Option.map_eq_some'.mp at this
    obtain ⟨val, ⟨h_some, h_val⟩⟩ := this
    rewrite [h_some, ←h_val]
    simp

  lemma padded_data_size (h_data: data.size < 136):
    (LeanCrypto.HashFunctions.multiratePadding 136 1 data).size = 136
  := by
    simp [
      LeanCrypto.HashFunctions.multiratePadding,
      LeanCrypto.HashFunctions.multiratePadding.totalLength,
      LeanCrypto.HashFunctions.multiratePadding.padlen,
      LeanCrypto.HashFunctions.multiratePadding.msglen,
      Nat.mod_eq_of_lt h_data,
      Nat.sub_add_cancel (Nat.le_of_lt h_data)
    ]
    apply Array.size_map

  lemma byte_array_append (a b: ByteArray): a ++ b = a.append b := by rfl

  lemma byte_array_empty_append : ByteArray.empty.append arr = arr := by
    unfold ByteArray.append ByteArray.copySlice
    simp [ByteArray.empty, ByteArray.mkEmpty]
    congr
    apply Array.extract_eq_self_iff.mpr
    simp [ByteArray.size]

  -- lemma byteArrayOfSHA3SR_of_byteArray {bytes: ByteArray} (h: bytes.size = 136):
  --   LeanCrypto.HashFunctions.byteArrayOfSHA3SR (LeanCrypto.HashFunctions.SHA3SRofByteArray bytes) =
  --   sorry
  -- := by
  --   simp [
  --     h,
  --     LeanCrypto.HashFunctions.byteArrayOfSHA3SR,
  --     LeanCrypto.HashFunctions.SHA3SRofByteArray
  --   ]
  --   rewrite [h]
  --   have := byte_array_empty_append (arr := bytes)
  --   simp [ByteArray.empty, ByteArray.mkEmpty] at this
  --   rewrite [byte_array_append, byte_array_append, this, h]
  --   simp
  --   rewrite [this]
  --   simp [ByteArray.foldl, ByteArray.foldlM, h]
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp
  --   unfold ByteArray.foldlM.loop; simp

  def padded_data_sha3r (padded_data: ByteArray) (h: padded_data.size = 136) :=#[
      padded_data[0].toUInt64 <<< 56 +
      padded_data[1].toUInt64 <<< 48 +
      padded_data[2].toUInt64 <<< 40 +
      padded_data[3].toUInt64 <<< 32 +
      padded_data[4].toUInt64 <<< 24 +
      padded_data[5].toUInt64 <<< 16 +
      padded_data[6].toUInt64 <<< 8 +
      padded_data[7].toUInt64,
      padded_data[8].toUInt64 <<< 56 +
      padded_data[9].toUInt64 <<< 48 +
      padded_data[10].toUInt64 <<< 40 +
      padded_data[11].toUInt64 <<< 32 +
      padded_data[12].toUInt64 <<< 24 +
      padded_data[13].toUInt64 <<< 16 +
      padded_data[14].toUInt64 <<< 8 +
      padded_data[15].toUInt64,
      padded_data[16].toUInt64 <<< 56 +
      padded_data[17].toUInt64 <<< 48 +
      padded_data[18].toUInt64 <<< 40 +
      padded_data[19].toUInt64 <<< 32 +
      padded_data[20].toUInt64 <<< 24 +
      padded_data[21].toUInt64 <<< 16 +
      padded_data[22].toUInt64 <<< 8 +
      padded_data[23].toUInt64,
      padded_data[24].toUInt64 <<< 56 +
      padded_data[25].toUInt64 <<< 48 +
      padded_data[26].toUInt64 <<< 40 +
      padded_data[27].toUInt64 <<< 32 +
      padded_data[28].toUInt64 <<< 24 +
      padded_data[29].toUInt64 <<< 16 +
      padded_data[30].toUInt64 <<< 8 +
      padded_data[31].toUInt64,
      padded_data[32].toUInt64 <<< 56 +
      padded_data[33].toUInt64 <<< 48 +
      padded_data[34].toUInt64 <<< 40 +
      padded_data[35].toUInt64 <<< 32 +
      padded_data[36].toUInt64 <<< 24 +
      padded_data[37].toUInt64 <<< 16 +
      padded_data[38].toUInt64 <<< 8 +
      padded_data[39].toUInt64,
      padded_data[40].toUInt64 <<< 56 +
      padded_data[41].toUInt64 <<< 48 +
      padded_data[42].toUInt64 <<< 40 +
      padded_data[43].toUInt64 <<< 32 +
      padded_data[44].toUInt64 <<< 24 +
      padded_data[45].toUInt64 <<< 16 +
      padded_data[46].toUInt64 <<< 8 +
      padded_data[47].toUInt64,
      padded_data[48].toUInt64 <<< 56 +
      padded_data[49].toUInt64 <<< 48 +
      padded_data[50].toUInt64 <<< 40 +
      padded_data[51].toUInt64 <<< 32 +
      padded_data[52].toUInt64 <<< 24 +
      padded_data[53].toUInt64 <<< 16 +
      padded_data[54].toUInt64 <<< 8 +
      padded_data[55].toUInt64,
      padded_data[56].toUInt64 <<< 56 +
      padded_data[57].toUInt64 <<< 48 +
      padded_data[58].toUInt64 <<< 40 +
      padded_data[59].toUInt64 <<< 32 +
      padded_data[60].toUInt64 <<< 24 +
      padded_data[61].toUInt64 <<< 16 +
      padded_data[62].toUInt64 <<< 8 +
      padded_data[63].toUInt64,
      padded_data[64].toUInt64 <<< 56 +
      padded_data[65].toUInt64 <<< 48 +
      padded_data[66].toUInt64 <<< 40 +
      padded_data[67].toUInt64 <<< 32 +
      padded_data[68].toUInt64 <<< 24 +
      padded_data[69].toUInt64 <<< 16 +
      padded_data[70].toUInt64 <<< 8 +
      padded_data[71].toUInt64,
      padded_data[72].toUInt64 <<< 56 +
      padded_data[73].toUInt64 <<< 48 +
      padded_data[74].toUInt64 <<< 40 +
      padded_data[75].toUInt64 <<< 32 +
      padded_data[76].toUInt64 <<< 24 +
      padded_data[77].toUInt64 <<< 16 +
      padded_data[78].toUInt64 <<< 8 +
      padded_data[79].toUInt64,
      padded_data[80].toUInt64 <<< 56 +
      padded_data[81].toUInt64 <<< 48 +
      padded_data[82].toUInt64 <<< 40 +
      padded_data[83].toUInt64 <<< 32 +
      padded_data[84].toUInt64 <<< 24 +
      padded_data[85].toUInt64 <<< 16 +
      padded_data[86].toUInt64 <<< 8 +
      padded_data[87].toUInt64,
      padded_data[88].toUInt64 <<< 56 +
      padded_data[89].toUInt64 <<< 48 +
      padded_data[90].toUInt64 <<< 40 +
      padded_data[91].toUInt64 <<< 32 +
      padded_data[92].toUInt64 <<< 24 +
      padded_data[93].toUInt64 <<< 16 +
      padded_data[94].toUInt64 <<< 8 +
      padded_data[95].toUInt64,
      padded_data[96].toUInt64 <<< 56 +
      padded_data[97].toUInt64 <<< 48 +
      padded_data[98].toUInt64 <<< 40 +
      padded_data[99].toUInt64 <<< 32 +
      padded_data[100].toUInt64 <<< 24 +
      padded_data[101].toUInt64 <<< 16 +
      padded_data[102].toUInt64 <<< 8 +
      padded_data[103].toUInt64,
      padded_data[104].toUInt64 <<< 56 +
      padded_data[105].toUInt64 <<< 48 +
      padded_data[106].toUInt64 <<< 40 +
      padded_data[107].toUInt64 <<< 32 +
      padded_data[108].toUInt64 <<< 24 +
      padded_data[109].toUInt64 <<< 16 +
      padded_data[110].toUInt64 <<< 8 +
      padded_data[111].toUInt64,
      padded_data[112].toUInt64 <<< 56 +
      padded_data[113].toUInt64 <<< 48 +
      padded_data[114].toUInt64 <<< 40 +
      padded_data[115].toUInt64 <<< 32 +
      padded_data[116].toUInt64 <<< 24 +
      padded_data[117].toUInt64 <<< 16 +
      padded_data[118].toUInt64 <<< 8 +
      padded_data[119].toUInt64,
      padded_data[120].toUInt64 <<< 56 +
      padded_data[121].toUInt64 <<< 48 +
      padded_data[122].toUInt64 <<< 40 +
      padded_data[123].toUInt64 <<< 32 +
      padded_data[124].toUInt64 <<< 24 +
      padded_data[125].toUInt64 <<< 16 +
      padded_data[126].toUInt64 <<< 8 +
      padded_data[127].toUInt64,
      padded_data[128].toUInt64 <<< 56 +
      padded_data[129].toUInt64 <<< 48 +
      padded_data[130].toUInt64 <<< 40 +
      padded_data[131].toUInt64 <<< 32 +
      padded_data[132].toUInt64 <<< 24 +
      padded_data[133].toUInt64 <<< 16 +
      padded_data[134].toUInt64 <<< 8 +
      padded_data[135].toUInt64
    ]

  set_option maxHeartbeats 400000
  lemma sha3sr_of_bytearray (padded_data: ByteArray) (h: padded_data.size = 136):
    LeanCrypto.HashFunctions.SHA3SRofByteArray padded_data =
    padded_data_sha3r padded_data h
  := by
    simp [LeanCrypto.HashFunctions.SHA3SRofByteArray, h, byte_array_append]
    have := byte_array_empty_append (arr := padded_data)
    simp [ByteArray.empty, ByteArray.mkEmpty] at this
    rewrite [this]
    simp [h]
    rewrite [show padded_data.size % 8 = 0 by simp [h]]
    simp
    rewrite [this]
    unfold ByteArray.foldl
    unfold ByteArray.foldlM; simp [h]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_one (byte: UInt8):
      (0: UInt64) + (72057594037927936: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 56
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_two (byte: UInt8):
      (281474976710656: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 48
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_three (byte: UInt8):
      (1099511627776: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 40
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_four (byte: UInt8):
      (4294967296: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 32
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_five (byte: UInt8):
      (16777216: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 24
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_six (byte: UInt8):
      (65536: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 16
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_seven (byte: UInt8):
      (256: UInt64) * byte.toUInt64 = byte.toUInt64 <<< 8
    := by
      apply UInt64.eq_of_toBitVec_eq
      simp; bv_decide
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    have h_byte_eight (byte: UInt8): (1: UInt64) * byte.toUInt64 = byte.toUInt64 := by
      apply UInt64.eq_of_toBitVec_eq
      simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_one]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_two]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_three]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_four]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_five]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_six]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_seven]
    unfold ByteArray.foldlM.loop; simp
    rewrite [h_byte_eight]
    unfold ByteArray.foldlM.loop; simp [Id.run]
    unfold padded_data_sha3r
    rfl


  set_option maxHeartbeats 800000
  example :
    LeanCrypto.HashFunctions.byteArrayOfSHA3SR (padded_data_sha3r padded_data h) =
    padded_data
  := by
    unfold LeanCrypto.HashFunctions.byteArrayOfSHA3SR
    have h_cell_1 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 56).toUInt8 = x1
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_2 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 48).toUInt8 = x2
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_3 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 40).toUInt8 = x3
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_4 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 32).toUInt8 = x4
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_5 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 24).toUInt8 = x5
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_6 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 16).toUInt8 = x6
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_7 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 8).toUInt8 = x7
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    have h_cell_8 (x1 x2 x3 x4 x5 x6 x7 x8: UInt8):
      ((x1.toUInt64 <<< 56 +
      x2.toUInt64 <<< 48 +
      x3.toUInt64 <<< 40 +
      x4.toUInt64 <<< 32 +
      x5.toUInt64 <<< 24 +
      x6.toUInt64 <<< 16 +
      x7.toUInt64 <<< 8 +
      x8.toUInt64) >>> 0).toUInt8 = x8
    := by
      apply UInt8.eq_of_toBitVec_eq
      simp
      bv_decide
    unfold padded_data_sha3r
    simp [←Array.foldl_toList, *, ByteArray.push.eq_def, Array.push, ByteArray.empty, ByteArray.mkEmpty]
    congr
    apply List.ext_get
    . simp [ByteArray.size] at h
      simp [h]
    . intro n h_n1 h_n2
      simp at h_n1
      simp [List.get_eq_getElem, List.get_eq_getElem]
      have : padded_data.1[n] = padded_data[n] := rfl
      simp [this]
      by_cases h_n : n ≥ 136; exfalso; omega
      by_cases h_n : n = 0; subst h_n; rfl
      by_cases h_n : n = 1; subst h_n; rfl
      by_cases h_n : n = 2; subst h_n; rfl
      by_cases h_n : n = 3; subst h_n; rfl
      by_cases h_n : n = 4; subst h_n; rfl
      by_cases h_n : n = 5; subst h_n; rfl
      by_cases h_n : n = 6; subst h_n; rfl
      by_cases h_n : n = 7; subst h_n; rfl
      by_cases h_n : n = 8; subst h_n; rfl
      by_cases h_n : n = 9; subst h_n; rfl
      by_cases h_n : n = 10; subst h_n; rfl
      by_cases h_n : n = 11; subst h_n; rfl
      by_cases h_n : n = 12; subst h_n; rfl
      by_cases h_n : n = 13; subst h_n; rfl
      by_cases h_n : n = 14; subst h_n; rfl
      by_cases h_n : n = 15; subst h_n; rfl
      by_cases h_n : n = 16; subst h_n; rfl
      by_cases h_n : n = 17; subst h_n; rfl
      by_cases h_n : n = 18; subst h_n; rfl
      by_cases h_n : n = 19; subst h_n; rfl
      by_cases h_n : n = 20; subst h_n; rfl
      by_cases h_n : n = 21; subst h_n; rfl
      by_cases h_n : n = 22; subst h_n; rfl
      by_cases h_n : n = 23; subst h_n; rfl
      by_cases h_n : n = 24; subst h_n; rfl
      by_cases h_n : n = 25; subst h_n; rfl
      by_cases h_n : n = 26; subst h_n; rfl
      by_cases h_n : n = 27; subst h_n; rfl
      by_cases h_n : n = 28; subst h_n; rfl
      by_cases h_n : n = 29; subst h_n; rfl
      by_cases h_n : n = 30; subst h_n; rfl
      by_cases h_n : n = 31; subst h_n; rfl
      by_cases h_n : n = 32; subst h_n; rfl
      by_cases h_n : n = 33; subst h_n; rfl
      by_cases h_n : n = 34; subst h_n; rfl
      by_cases h_n : n = 35; subst h_n; rfl
      by_cases h_n : n = 36; subst h_n; rfl
      by_cases h_n : n = 37; subst h_n; rfl
      by_cases h_n : n = 38; subst h_n; rfl
      by_cases h_n : n = 39; subst h_n; rfl
      by_cases h_n : n = 40; subst h_n; rfl
      by_cases h_n : n = 41; subst h_n; rfl
      by_cases h_n : n = 42; subst h_n; rfl
      by_cases h_n : n = 43; subst h_n; rfl
      by_cases h_n : n = 44; subst h_n; rfl
      by_cases h_n : n = 45; subst h_n; rfl
      by_cases h_n : n = 46; subst h_n; rfl
      by_cases h_n : n = 47; subst h_n; rfl
      by_cases h_n : n = 48; subst h_n; rfl
      by_cases h_n : n = 49; subst h_n; rfl
      by_cases h_n : n = 50; subst h_n; rfl
      by_cases h_n : n = 51; subst h_n; rfl
      by_cases h_n : n = 52; subst h_n; rfl
      by_cases h_n : n = 53; subst h_n; rfl
      by_cases h_n : n = 54; subst h_n; rfl
      by_cases h_n : n = 55; subst h_n; rfl
      by_cases h_n : n = 56; subst h_n; rfl
      by_cases h_n : n = 57; subst h_n; rfl
      by_cases h_n : n = 58; subst h_n; rfl
      by_cases h_n : n = 59; subst h_n; rfl
      by_cases h_n : n = 60; subst h_n; rfl
      by_cases h_n : n = 61; subst h_n; rfl
      by_cases h_n : n = 62; subst h_n; rfl
      by_cases h_n : n = 63; subst h_n; rfl
      by_cases h_n : n = 64; subst h_n; rfl
      by_cases h_n : n = 65; subst h_n; rfl
      by_cases h_n : n = 66; subst h_n; rfl
      by_cases h_n : n = 67; subst h_n; rfl
      by_cases h_n : n = 68; subst h_n; rfl
      by_cases h_n : n = 69; subst h_n; rfl
      by_cases h_n : n = 70; subst h_n; rfl
      by_cases h_n : n = 71; subst h_n; rfl
      by_cases h_n : n = 72; subst h_n; rfl
      by_cases h_n : n = 73; subst h_n; rfl
      by_cases h_n : n = 74; subst h_n; rfl
      by_cases h_n : n = 75; subst h_n; rfl
      by_cases h_n : n = 76; subst h_n; rfl
      by_cases h_n : n = 77; subst h_n; rfl
      by_cases h_n : n = 78; subst h_n; rfl
      by_cases h_n : n = 79; subst h_n; rfl
      by_cases h_n : n = 80; subst h_n; rfl
      by_cases h_n : n = 81; subst h_n; rfl
      by_cases h_n : n = 82; subst h_n; rfl
      by_cases h_n : n = 83; subst h_n; rfl
      by_cases h_n : n = 84; subst h_n; rfl
      by_cases h_n : n = 85; subst h_n; rfl
      by_cases h_n : n = 86; subst h_n; rfl
      by_cases h_n : n = 87; subst h_n; rfl
      by_cases h_n : n = 88; subst h_n; rfl
      by_cases h_n : n = 89; subst h_n; rfl
      by_cases h_n : n = 90; subst h_n; rfl
      by_cases h_n : n = 91; subst h_n; rfl
      by_cases h_n : n = 92; subst h_n; rfl
      by_cases h_n : n = 93; subst h_n; rfl
      by_cases h_n : n = 94; subst h_n; rfl
      by_cases h_n : n = 95; subst h_n; rfl
      by_cases h_n : n = 96; subst h_n; rfl
      by_cases h_n : n = 97; subst h_n; rfl
      by_cases h_n : n = 98; subst h_n; rfl
      by_cases h_n : n = 99; subst h_n; rfl
      by_cases h_n : n = 100; subst h_n; rfl
      by_cases h_n : n = 101; subst h_n; rfl
      by_cases h_n : n = 102; subst h_n; rfl
      by_cases h_n : n = 103; subst h_n; rfl
      by_cases h_n : n = 104; subst h_n; rfl
      by_cases h_n : n = 105; subst h_n; rfl
      by_cases h_n : n = 106; subst h_n; rfl
      by_cases h_n : n = 107; subst h_n; rfl
      by_cases h_n : n = 108; subst h_n; rfl
      by_cases h_n : n = 109; subst h_n; rfl
      by_cases h_n : n = 110; subst h_n; rfl
      by_cases h_n : n = 111; subst h_n; rfl
      by_cases h_n : n = 112; subst h_n; rfl
      by_cases h_n : n = 113; subst h_n; rfl
      by_cases h_n : n = 114; subst h_n; rfl
      by_cases h_n : n = 115; subst h_n; rfl
      by_cases h_n : n = 116; subst h_n; rfl
      by_cases h_n : n = 117; subst h_n; rfl
      by_cases h_n : n = 118; subst h_n; rfl
      by_cases h_n : n = 119; subst h_n; rfl
      by_cases h_n : n = 120; subst h_n; rfl
      by_cases h_n : n = 121; subst h_n; rfl
      by_cases h_n : n = 122; subst h_n; rfl
      by_cases h_n : n = 123; subst h_n; rfl
      by_cases h_n : n = 124; subst h_n; rfl
      by_cases h_n : n = 125; subst h_n; rfl
      by_cases h_n : n = 126; subst h_n; rfl
      by_cases h_n : n = 127; subst h_n; rfl
      by_cases h_n : n = 128; subst h_n; rfl
      by_cases h_n : n = 129; subst h_n; rfl
      by_cases h_n : n = 130; subst h_n; rfl
      by_cases h_n : n = 131; subst h_n; rfl
      by_cases h_n : n = 132; subst h_n; rfl
      by_cases h_n : n = 133; subst h_n; rfl
      by_cases h_n : n = 134; subst h_n; rfl
      by_cases h_n : n = 135; subst h_n; rfl
      exfalso; omega





  -- example (h_data: data.size < 136):
  --   LeanCrypto.HashFunctions.keccak256 data = sorry
  -- := by
  --   simp [
  --     LeanCrypto.HashFunctions.keccak256,
  --     LeanCrypto.HashFunctions.hashFunction,
  --     LeanCrypto.HashFunctions.paddingKeccak,
  --     LeanCrypto.HashFunctions.hashFunction.outputBytes
  --   ]
  --   set padded_data := LeanCrypto.HashFunctions.multiratePadding 136 1 data
  --   have h_padded_data_size: padded_data.size = 136 := padded_data_size h_data
  --   simp [ByteArray.size] at h_padded_data_size
  --   simp [LeanCrypto.HashFunctions.SHA3SRofByteArray]
  --   simp [ByteArray.size, h_padded_data_size]
  --   rewrite [h_padded_data_size]
  --   have (arr: ByteArray) : ByteArray.empty.append arr = arr := by
  --     unfold ByteArray.append ByteArray.copySlice
  --     simp [ByteArray.empty, ByteArray.mkEmpty]
  --     congr
  --     apply Array.extract_eq_self_iff.mpr
  --     simp [ByteArray.size]
  --   simp [ByteArray.empty, ByteArray.mkEmpty] at this
  --   simp [byte_array_append]
  --   rewrite [this, h_padded_data_size]
  --   unfold ByteArray.foldl ByteArray.foldlM
  --   simp [ByteArray.size, h_padded_data_size]
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp
  --   unfold ByteArray.foldlM.loop
  --   simp [Id.run]
  --   simp [LeanCrypto.HashFunctions.byteArrayOfSHA3SR]
  --   sorry

end Keccak.Soundness

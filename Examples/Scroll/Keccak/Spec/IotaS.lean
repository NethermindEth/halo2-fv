import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  lemma rho_pi_chi_cells_address (p i j idx: ℕ) (hp: p < 3) (hi: i < 5) (hj: j < 5) (hidx: idx < 16): rho_pi_chi_cells c round (OfNat.ofNat p) (OfNat.ofNat i) (OfNat.ofNat j) (OfNat.ofNat idx) =
      cell_manager c round (336 + p * 420 + (idx + j * 16) % 12 + i * 12 + (idx + j * 16) / 12 * 60) := by
      have hidx': idx < rho_by_pi_num_word_parts := by simp only [rho_by_pi_num_word_parts_val, hidx]
      unfold rho_pi_chi_cells
      dsimp only
      simp only [keccak_constants]
      norm_num
      simp only [OfNat.ofNat, Nat.mod_eq_of_lt, hp, hi, hj, hidx']
      simp only [mul_assoc, Nat.reduceMul]

  @[to_iota_s] lemma to_os'_0_0: Decode.expr [
      (4, cell_manager c round 1176),
      (4, cell_manager c round 1177),
      (4, cell_manager c round 1178),
      (4, cell_manager c round 1179),
      (4, cell_manager c round 1180),
      (4, cell_manager c round 1181),
      (4, cell_manager c round 1182),
      (4, cell_manager c round 1183),
      (4, cell_manager c round 1184),
      (4, cell_manager c round 1185),
      (4, cell_manager c round 1186),
      (4, cell_manager c round 1187),
      (4, cell_manager c round 1236),
      (4, cell_manager c round 1237),
      (4, cell_manager c round 1238),
      (4, cell_manager c round 1239),
    ] = os' c round 0 0 := by
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 0 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 0 0 15 (by trivial) (by trivial) (by trivial) ( by trivial)]

  @[to_iota_s] lemma to_iota_s_0_0: Decode.expr
    [(6, cell_manager c round 1644), (6, cell_manager c round 1645), (6, cell_manager c round 1646),
      (6, cell_manager c round 1647), (6, cell_manager c round 1648), (6, cell_manager c round 1649),
      (6, cell_manager c round 1650), (6, cell_manager c round 1651), (6, cell_manager c round 1652),
      (6, cell_manager c round 1653), (4, cell_manager c round 1654)] = iota_s c round 0 0 := by
    unfold iota_s
    dsimp only
    congr
    simp only [keccak_constants]
    unfold Transform.split_expr_old
    norm_num
    unfold Split.expr_res
    simp only [word_parts_known]
    rfl
  @[to_iota_s] lemma to_iota_s_0_1: Decode.expr
    [(4, cell_manager c round 1240), (4, cell_manager c round 1241), (4, cell_manager c round 1242),
      (4, cell_manager c round 1243), (4, cell_manager c round 1244), (4, cell_manager c round 1245),
      (4, cell_manager c round 1246), (4, cell_manager c round 1247), (4, cell_manager c round 1296),
      (4, cell_manager c round 1297), (4, cell_manager c round 1298), (4, cell_manager c round 1299),
      (4, cell_manager c round 1300), (4, cell_manager c round 1301), (4, cell_manager c round 1302),
      (4, cell_manager c round 1303)] = iota_s c round 0 1 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 1 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 0 1 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_0_2: Decode.expr
    [(4, cell_manager c round 1304), (4, cell_manager c round 1305), (4, cell_manager c round 1306),
      (4, cell_manager c round 1307), (4, cell_manager c round 1356), (4, cell_manager c round 1357),
      (4, cell_manager c round 1358), (4, cell_manager c round 1359), (4, cell_manager c round 1360),
      (4, cell_manager c round 1361), (4, cell_manager c round 1362), (4, cell_manager c round 1363),
      (4, cell_manager c round 1364), (4, cell_manager c round 1365), (4, cell_manager c round 1366),
      (4, cell_manager c round 1367)] = iota_s c round 0 2 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 2 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 0 2 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_0_3: Decode.expr
    [(4, cell_manager c round 1416), (4, cell_manager c round 1417), (4, cell_manager c round 1418),
      (4, cell_manager c round 1419), (4, cell_manager c round 1420), (4, cell_manager c round 1421),
      (4, cell_manager c round 1422), (4, cell_manager c round 1423), (4, cell_manager c round 1424),
      (4, cell_manager c round 1425), (4, cell_manager c round 1426), (4, cell_manager c round 1427),
      (4, cell_manager c round 1476), (4, cell_manager c round 1477), (4, cell_manager c round 1478),
      (4, cell_manager c round 1479)] = iota_s c round 0 3 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 3 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 0 3 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_0_4: Decode.expr
    [(4, cell_manager c round 1480), (4, cell_manager c round 1481), (4, cell_manager c round 1482),
      (4, cell_manager c round 1483), (4, cell_manager c round 1484), (4, cell_manager c round 1485),
      (4, cell_manager c round 1486), (4, cell_manager c round 1487), (4, cell_manager c round 1536),
      (4, cell_manager c round 1537), (4, cell_manager c round 1538), (4, cell_manager c round 1539),
      (4, cell_manager c round 1540), (4, cell_manager c round 1541), (4, cell_manager c round 1542),
      (4, cell_manager c round 1543)] = iota_s c round 0 4 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 0 4 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 0 4 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_1_0: Decode.expr
    [(4, cell_manager c round 1188), (4, cell_manager c round 1189), (4, cell_manager c round 1190),
      (4, cell_manager c round 1191), (4, cell_manager c round 1192), (4, cell_manager c round 1193),
      (4, cell_manager c round 1194), (4, cell_manager c round 1195), (4, cell_manager c round 1196),
      (4, cell_manager c round 1197), (4, cell_manager c round 1198), (4, cell_manager c round 1199),
      (4, cell_manager c round 1248), (4, cell_manager c round 1249), (4, cell_manager c round 1250),
      (4, cell_manager c round 1251)] = iota_s c round 1 0 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 0 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 1 0 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_1_1: Decode.expr
    [(4, cell_manager c round 1252), (4, cell_manager c round 1253), (4, cell_manager c round 1254),
      (4, cell_manager c round 1255), (4, cell_manager c round 1256), (4, cell_manager c round 1257),
      (4, cell_manager c round 1258), (4, cell_manager c round 1259), (4, cell_manager c round 1308),
      (4, cell_manager c round 1309), (4, cell_manager c round 1310), (4, cell_manager c round 1311),
      (4, cell_manager c round 1312), (4, cell_manager c round 1313), (4, cell_manager c round 1314),
      (4, cell_manager c round 1315)] = iota_s c round 1 1 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 1 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 1 1 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_1_2: Decode.expr
    [(4, cell_manager c round 1316), (4, cell_manager c round 1317), (4, cell_manager c round 1318),
      (4, cell_manager c round 1319), (4, cell_manager c round 1368), (4, cell_manager c round 1369),
      (4, cell_manager c round 1370), (4, cell_manager c round 1371), (4, cell_manager c round 1372),
      (4, cell_manager c round 1373), (4, cell_manager c round 1374), (4, cell_manager c round 1375),
      (4, cell_manager c round 1376), (4, cell_manager c round 1377), (4, cell_manager c round 1378),
      (4, cell_manager c round 1379)] = iota_s c round 1 2 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 2 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 1 2 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_1_3: Decode.expr
    [(4, cell_manager c round 1428), (4, cell_manager c round 1429), (4, cell_manager c round 1430),
      (4, cell_manager c round 1431), (4, cell_manager c round 1432), (4, cell_manager c round 1433),
      (4, cell_manager c round 1434), (4, cell_manager c round 1435), (4, cell_manager c round 1436),
      (4, cell_manager c round 1437), (4, cell_manager c round 1438), (4, cell_manager c round 1439),
      (4, cell_manager c round 1488), (4, cell_manager c round 1489), (4, cell_manager c round 1490),
      (4, cell_manager c round 1491)] = iota_s c round 1 3 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 3 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 1 3 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_1_4: Decode.expr
    [(4, cell_manager c round 1492), (4, cell_manager c round 1493), (4, cell_manager c round 1494),
      (4, cell_manager c round 1495), (4, cell_manager c round 1496), (4, cell_manager c round 1497),
      (4, cell_manager c round 1498), (4, cell_manager c round 1499), (4, cell_manager c round 1548),
      (4, cell_manager c round 1549), (4, cell_manager c round 1550), (4, cell_manager c round 1551),
      (4, cell_manager c round 1552), (4, cell_manager c round 1553), (4, cell_manager c round 1554),
      (4, cell_manager c round 1555)] = iota_s c round 1 4 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 1 4 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 1 4 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_2_0: Decode.expr
    [(4, cell_manager c round 1200), (4, cell_manager c round 1201),
      (4, cell_manager c round 1202), (4, cell_manager c round 1203),
      (4, cell_manager c round 1204), (4, cell_manager c round 1205),
      (4, cell_manager c round 1206), (4, cell_manager c round 1207),
      (4, cell_manager c round 1208), (4, cell_manager c round 1209),
      (4, cell_manager c round 1210), (4, cell_manager c round 1211),
      (4, cell_manager c round 1260), (4, cell_manager c round 1261), (4, cell_manager c round 1262),
      (4, cell_manager c round 1263)] = iota_s c round 2 0 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 0 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 2 0 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_2_1: Decode.expr
    [(4, cell_manager c round 1264), (4, cell_manager c round 1265), (4, cell_manager c round 1266),
      (4, cell_manager c round 1267), (4, cell_manager c round 1268), (4, cell_manager c round 1269),
      (4, cell_manager c round 1270), (4, cell_manager c round 1271), (4, cell_manager c round 1320),
      (4, cell_manager c round 1321), (4, cell_manager c round 1322), (4, cell_manager c round 1323),
      (4, cell_manager c round 1324), (4, cell_manager c round 1325), (4, cell_manager c round 1326),
      (4, cell_manager c round 1327)] = iota_s c round 2 1 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 1 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 2 1 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_2_2: Decode.expr
    [(4, cell_manager c round 1328), (4, cell_manager c round 1329), (4, cell_manager c round 1330),
      (4, cell_manager c round 1331), (4, cell_manager c round 1380), (4, cell_manager c round 1381),
      (4, cell_manager c round 1382), (4, cell_manager c round 1383), (4, cell_manager c round 1384),
      (4, cell_manager c round 1385), (4, cell_manager c round 1386), (4, cell_manager c round 1387),
      (4, cell_manager c round 1388), (4, cell_manager c round 1389), (4, cell_manager c round 1390),
      (4, cell_manager c round 1391)] = iota_s c round 2 2 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 2 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 2 2 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_2_3: Decode.expr
    [(4, cell_manager c round 1440), (4, cell_manager c round 1441), (4, cell_manager c round 1442),
      (4, cell_manager c round 1443), (4, cell_manager c round 1444), (4, cell_manager c round 1445),
      (4, cell_manager c round 1446), (4, cell_manager c round 1447), (4, cell_manager c round 1448),
      (4, cell_manager c round 1449), (4, cell_manager c round 1450), (4, cell_manager c round 1451),
      (4, cell_manager c round 1500), (4, cell_manager c round 1501), (4, cell_manager c round 1502),
      (4, cell_manager c round 1503)] = iota_s c round 2 3 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 3 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 2 3 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_2_4: Decode.expr
    [(4, cell_manager c round 1504), (4, cell_manager c round 1505), (4, cell_manager c round 1506),
      (4, cell_manager c round 1507), (4, cell_manager c round 1508), (4, cell_manager c round 1509),
      (4, cell_manager c round 1510), (4, cell_manager c round 1511), (4, cell_manager c round 1560),
      (4, cell_manager c round 1561), (4, cell_manager c round 1562), (4, cell_manager c round 1563),
      (4, cell_manager c round 1564), (4, cell_manager c round 1565), (4, cell_manager c round 1566),
      (4, cell_manager c round 1567)] = iota_s c round 2 4 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 2 4 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 2 4 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_3_0: Decode.expr
    [(4, cell_manager c round 1212), (4, cell_manager c round 1213), (4, cell_manager c round 1214),
      (4, cell_manager c round 1215), (4, cell_manager c round 1216), (4, cell_manager c round 1217),
      (4, cell_manager c round 1218), (4, cell_manager c round 1219), (4, cell_manager c round 1220),
      (4, cell_manager c round 1221), (4, cell_manager c round 1222), (4, cell_manager c round 1223),
      (4, cell_manager c round 1272), (4, cell_manager c round 1273), (4, cell_manager c round 1274),
      (4, cell_manager c round 1275)] = iota_s c round 3 0 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 0 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 3 0 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_3_1: Decode.expr
    [(4, cell_manager c round 1276), (4, cell_manager c round 1277), (4, cell_manager c round 1278),
      (4, cell_manager c round 1279), (4, cell_manager c round 1280), (4, cell_manager c round 1281),
      (4, cell_manager c round 1282), (4, cell_manager c round 1283), (4, cell_manager c round 1332),
      (4, cell_manager c round 1333), (4, cell_manager c round 1334), (4, cell_manager c round 1335),
      (4, cell_manager c round 1336), (4, cell_manager c round 1337), (4, cell_manager c round 1338),
      (4, cell_manager c round 1339)] = iota_s c round 3 1 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 1 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 3 1 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_3_2: Decode.expr
    [(4, cell_manager c round 1340), (4, cell_manager c round 1341), (4, cell_manager c round 1342),
      (4, cell_manager c round 1343), (4, cell_manager c round 1392), (4, cell_manager c round 1393),
      (4, cell_manager c round 1394), (4, cell_manager c round 1395), (4, cell_manager c round 1396),
      (4, cell_manager c round 1397), (4, cell_manager c round 1398), (4, cell_manager c round 1399),
      (4, cell_manager c round 1400), (4, cell_manager c round 1401), (4, cell_manager c round 1402),
      (4, cell_manager c round 1403)] = iota_s c round 3 2 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 2 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 3 2 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_3_3: Decode.expr
    [(4, cell_manager c round 1452), (4, cell_manager c round 1453), (4, cell_manager c round 1454),
      (4, cell_manager c round 1455), (4, cell_manager c round 1456), (4, cell_manager c round 1457),
      (4, cell_manager c round 1458), (4, cell_manager c round 1459), (4, cell_manager c round 1460),
      (4, cell_manager c round 1461), (4, cell_manager c round 1462), (4, cell_manager c round 1463),
      (4, cell_manager c round 1512), (4, cell_manager c round 1513), (4, cell_manager c round 1514),
      (4, cell_manager c round 1515)] = iota_s c round 3 3 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 3 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 3 3 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_3_4: Decode.expr
    [(4, cell_manager c round 1516), (4, cell_manager c round 1517), (4, cell_manager c round 1518),
      (4, cell_manager c round 1519), (4, cell_manager c round 1520), (4, cell_manager c round 1521),
      (4, cell_manager c round 1522), (4, cell_manager c round 1523), (4, cell_manager c round 1572),
      (4, cell_manager c round 1573), (4, cell_manager c round 1574), (4, cell_manager c round 1575),
      (4, cell_manager c round 1576), (4, cell_manager c round 1577), (4, cell_manager c round 1578),
      (4, cell_manager c round 1579)] = iota_s c round 3 4 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 3 4 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 3 4 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_4_0: Decode.expr
    [(4, cell_manager c round 1224), (4, cell_manager c round 1225), (4, cell_manager c round 1226),
      (4, cell_manager c round 1227), (4, cell_manager c round 1228), (4, cell_manager c round 1229),
      (4, cell_manager c round 1230), (4, cell_manager c round 1231), (4, cell_manager c round 1232),
      (4, cell_manager c round 1233), (4, cell_manager c round 1234), (4, cell_manager c round 1235),
      (4, cell_manager c round 1284), (4, cell_manager c round 1285), (4, cell_manager c round 1286),
      (4, cell_manager c round 1287)]= iota_s c round 4 0 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 0 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 4 0 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_4_1: Decode.expr
    [(4, cell_manager c round 1288), (4, cell_manager c round 1289), (4, cell_manager c round 1290),
      (4, cell_manager c round 1291), (4, cell_manager c round 1292), (4, cell_manager c round 1293),
      (4, cell_manager c round 1294), (4, cell_manager c round 1295), (4, cell_manager c round 1344),
      (4, cell_manager c round 1345), (4, cell_manager c round 1346), (4, cell_manager c round 1347),
      (4, cell_manager c round 1348), (4, cell_manager c round 1349), (4, cell_manager c round 1350),
      (4, cell_manager c round 1351)] = iota_s c round 4 1 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 1 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 4 1 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_4_2: Decode.expr
    [(4, cell_manager c round 1352), (4, cell_manager c round 1353), (4, cell_manager c round 1354),
      (4, cell_manager c round 1355), (4, cell_manager c round 1404), (4, cell_manager c round 1405),
      (4, cell_manager c round 1406), (4, cell_manager c round 1407), (4, cell_manager c round 1408),
      (4, cell_manager c round 1409), (4, cell_manager c round 1410), (4, cell_manager c round 1411),
      (4, cell_manager c round 1412), (4, cell_manager c round 1413), (4, cell_manager c round 1414),
      (4, cell_manager c round 1415)] = iota_s c round 4 2 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 2 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 4 2 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_4_3: Decode.expr
    [(4, cell_manager c round 1464), (4, cell_manager c round 1465), (4, cell_manager c round 1466),
      (4, cell_manager c round 1467), (4, cell_manager c round 1468), (4, cell_manager c round 1469),
      (4, cell_manager c round 1470), (4, cell_manager c round 1471), (4, cell_manager c round 1472),
      (4, cell_manager c round 1473), (4, cell_manager c round 1474), (4, cell_manager c round 1475),
      (4, cell_manager c round 1524), (4, cell_manager c round 1525), (4, cell_manager c round 1526),
      (4, cell_manager c round 1527)] = iota_s c round 4 3 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 3 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 4 3 15 (by trivial) (by trivial) (by trivial) ( by trivial)]
  @[to_iota_s] lemma to_iota_s_4_4: Decode.expr
    [(4, cell_manager c round 1528), (4, cell_manager c round 1529), (4, cell_manager c round 1530),
      (4, cell_manager c round 1531), (4, cell_manager c round 1532), (4, cell_manager c round 1533),
      (4, cell_manager c round 1534), (4, cell_manager c round 1535), (4, cell_manager c round 1584),
      (4, cell_manager c round 1585), (4, cell_manager c round 1586), (4, cell_manager c round 1587),
      (4, cell_manager c round 1588), (4, cell_manager c round 1589), (4, cell_manager c round 1590),
      (4, cell_manager c round 1591)] = iota_s c round 4 4 := by
    unfold iota_s
    dsimp only
    unfold os'
    congr
    simp only [keccak_constants]
    simp only [List.range, List.range.loop]
    simp only [List.map]
    simp only [Fin.isValue, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 0 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 1 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 2 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 3 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 4 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 5 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 6 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 7 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 8 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 9 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 10 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 11 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 12 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 13 (by trivial) (by trivial) (by trivial) ( by trivial)]
    apply And.intro; rw [rho_pi_chi_cells_address 2 4 4 14 (by trivial) (by trivial) (by trivial) ( by trivial)]
    rw [rho_pi_chi_cells_address 2 4 4 15 (by trivial) (by trivial) (by trivial) ( by trivial)]

end Keccak

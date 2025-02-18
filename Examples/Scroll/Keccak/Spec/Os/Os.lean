import Examples.Scroll.Keccak.Spec.Program
import Examples.Scroll.Keccak.Spec.KeccakConstants

namespace Keccak

  @[to_os] lemma os_0_0: cell_manager c round 0 + t c round 0 = os c round 0 0 := rfl
  @[to_os] lemma os_0_1: cell_manager c round 1 + t c round 0 = os c round 0 1 := rfl
  @[to_os] lemma os_0_2: cell_manager c round 2 + t c round 0 = os c round 0 2 := rfl
  @[to_os] lemma os_0_3: cell_manager c round 3 + t c round 0 = os c round 0 3 := rfl
  @[to_os] lemma os_0_4: cell_manager c round 4 + t c round 0 = os c round 0 4 := rfl
  @[to_os] lemma os_1_0: cell_manager c round 5 + t c round 1 = os c round 1 0 := rfl
  @[to_os] lemma os_1_1: cell_manager c round 6 + t c round 1 = os c round 1 1 := rfl
  @[to_os] lemma os_1_2: cell_manager c round 7 + t c round 1 = os c round 1 2 := rfl
  @[to_os] lemma os_1_3: cell_manager c round 8 + t c round 1 = os c round 1 3 := rfl
  @[to_os] lemma os_1_4: cell_manager c round 9 + t c round 1 = os c round 1 4 := rfl
  @[to_os] lemma os_2_0: cell_manager c round 10 + t c round 2 = os c round 2 0 := rfl
  @[to_os] lemma os_2_1: cell_manager c round 11 + t c round 2 = os c round 2 1 := rfl
  @[to_os] lemma os_2_2: cell_manager c round 12 + t c round 2 = os c round 2 2 := rfl
  @[to_os] lemma os_2_3: cell_manager c round 13 + t c round 2 = os c round 2 3 := rfl
  @[to_os] lemma os_2_4: cell_manager c round 14 + t c round 2 = os c round 2 4 := rfl
  @[to_os] lemma os_3_0: cell_manager c round 15 + t c round 3 = os c round 3 0 := rfl
  @[to_os] lemma os_3_1: cell_manager c round 16 + t c round 3 = os c round 3 1 := rfl
  @[to_os] lemma os_3_2: cell_manager c round 17 + t c round 3 = os c round 3 2 := rfl
  @[to_os] lemma os_3_3: cell_manager c round 18 + t c round 3 = os c round 3 3 := rfl
  @[to_os] lemma os_3_4: cell_manager c round 19 + t c round 3 = os c round 3 4 := rfl
  @[to_os] lemma os_4_0: cell_manager c round 20 + t c round 4 = os c round 4 0 := rfl
  @[to_os] lemma os_4_1: cell_manager c round 21 + t c round 4 = os c round 4 1 := rfl
  @[to_os] lemma os_4_2: cell_manager c round 22 + t c round 4 = os c round 4 2 := rfl
  @[to_os] lemma os_4_3: cell_manager c round 23 + t c round 4 = os c round 4 3 := rfl
  @[to_os] lemma os_4_4: cell_manager c round 24 + t c round 4 = os c round 4 4 := rfl

end Keccak

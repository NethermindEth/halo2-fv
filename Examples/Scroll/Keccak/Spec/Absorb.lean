import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  namespace Absorb
    @[to_absorb] lemma to_absorb_from: cell_manager c round 25 = absorb_from c round := rfl
    @[to_absorb] lemma to_absorb_data: cell_manager c round 26 = absorb_data c round := rfl
    @[to_absorb] lemma to_absorb_result: cell_manager c round 27 = absorb_result c round := rfl
  end Absorb
end Keccak

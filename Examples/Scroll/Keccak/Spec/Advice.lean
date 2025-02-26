import Examples.Scroll.Keccak.Attributes
import Examples.Scroll.Keccak.Spec.Program

namespace Keccak.Advice
  @[to_named_advice] lemma to_is_final: c.get_advice 0 row = is_final c row := rfl
  @[to_named_advice] lemma to_data_rlc: c.get_advice 1 row = data_rlc c row := rfl
  @[to_named_advice] lemma to_length: c.get_advice 2 row = length c row := rfl
  @[to_named_advice] lemma to_hash_rlc: c.get_advice 3 row = hash_rlc c row := rfl
end Keccak.Advice

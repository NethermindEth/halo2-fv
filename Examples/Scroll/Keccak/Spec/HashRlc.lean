import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  lemma to_hash_rlc: c.get_advice 3 row = hash_rlc c row := rfl
end Keccak

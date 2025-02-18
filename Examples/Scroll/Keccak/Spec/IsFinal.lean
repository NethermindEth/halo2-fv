import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  lemma to_is_final: c.get_advice 0 row = is_final c row := rfl
end Keccak

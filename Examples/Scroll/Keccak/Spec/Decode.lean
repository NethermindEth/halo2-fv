import Examples.Scroll.Keccak.Spec.Program

namespace Keccak
  namespace Decode
    @[to_decode] lemma to_decode_nil {P: ℕ}: (0: ZMod P) = expr [] := by rfl
    @[to_decode] lemma to_decode_cons_1 {x: ZMod P}: 8 * expr l + x = expr ((1,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_2 {x: ZMod P}: 64 * expr l + x = expr ((2,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_3 {x: ZMod P}: 512 * expr l + x = expr ((3,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_4 {x: ZMod P}: 4096 * expr l + x = expr ((4,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
    @[to_decode] lemma to_decode_cons_6 {x: ZMod P}: 262144 * expr l + x = expr ((6,x)::l) := by
      unfold expr; simp [List.foldr_cons, keccak_constants, zmod_pow_simps]
  end Decode
end Keccak

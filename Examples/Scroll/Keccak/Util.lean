import Examples.Scroll.Keccak.Attributes
import Examples.Scroll.Keccak.Constants
import Examples.Scroll.Keccak.Extraction

namespace Keccak
  namespace ValidCircuit

    def get_advice_wrapped (c: ValidCircuit P P_Prime) (column row rotation: ℕ): ZMod P :=
      c.get_advice column ((row + rotation) % c.n)

    lemma get_advice_wrapped_zero (c: ValidCircuit P P_Prime) (h_row: row < c.n) :
      c.get_advice_wrapped column row 0 = c.get_advice column row := by
        unfold get_advice_wrapped
        simp only [add_zero, Nat.mod_eq_of_lt h_row]

  end ValidCircuit

  def get_rotate_count (count part_size: ℕ) : ℕ :=
    (count + part_size - 1) / part_size

  def target_part_sizes (part_size: ℕ): List ℕ :=
    ((List.range NUM_BITS_PER_WORD).toChunks part_size).map List.length

  def target_part_sizes_rot (part_size rot: ℕ) :=
    ((List.ranges [rot, NUM_BITS_PER_WORD - rot]
    ).map (fun l => (l.toChunks part_size).map List.length)
    ).join

  @[target_part_sizes_known] lemma target_part_sizes_to_rot: target_part_sizes k = target_part_sizes_rot k 0 := by
    unfold target_part_sizes target_part_sizes_rot
    simp [List.ranges]
    simp [List.toChunks]

  @[target_part_sizes_known] lemma target_part_sizes_4_0: target_part_sizes_rot 4 0 = [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := rfl

  namespace WordParts

    def new_uniform (part_size rot: ℕ): List (List ℕ) :=
      let bits := List.rotateRight (List.range 64) rot
      let chunked_bits := bits.toChunks part_size
      let split_chunks := (chunked_bits.map (fun chunk =>
        let split := chunk.splitAt (chunk.findIdx (λ x => x = 0))
        [split.fst, split.snd]
      )).join.filter (λ l => l ≠ [])
      let rot_idx := split_chunks.findIdx (λ l => l.contains 0)
      split_chunks.rotateLeft rot_idx

    def new_non_uniform (part_size rot: ℕ): List (List ℕ) :=
      let bits := List.rotateRight (List.range 64) rot
      let bits_start := bits.take rot
      let bits_end := bits.drop rot
      let chunked_bits_start := bits_start.toChunks part_size
      let chunked_bits_end := bits_end.toChunks part_size
      chunked_bits_end.append chunked_bits_start

    def new (part_size rot: ℕ) (uniform: Bool): List (List ℕ) :=
      if uniform
      then new_uniform part_size rot
      else new_non_uniform part_size rot

    @[word_parts_known] lemma new_3_0_false : new 3 0 false = [
      [0, 1, 2],
      [3, 4, 5],
      [6, 7, 8],
      [9, 10, 11],
      [12, 13, 14],
      [15, 16, 17],
      [18, 19, 20],
      [21, 22, 23],
      [24, 25, 26],
      [27, 28, 29],
      [30, 31, 32],
      [33, 34, 35],
      [36, 37, 38],
      [39, 40, 41],
      [42, 43, 44],
      [45, 46, 47],
      [48, 49, 50],
      [51, 52, 53],
      [54, 55, 56],
      [57, 58, 59],
      [60, 61, 62],
      [63]
    ] := by decide

    @[word_parts_known] lemma new_3_1_false: new 3 1 false = [
      [0, 1, 2],
      [3, 4, 5],
      [6, 7, 8],
      [9, 10, 11],
      [12, 13, 14],
      [15, 16, 17],
      [18, 19, 20],
      [21, 22, 23],
      [24, 25, 26],
      [27, 28, 29],
      [30, 31, 32],
      [33, 34, 35],
      [36, 37, 38],
      [39, 40, 41],
      [42, 43, 44],
      [45, 46, 47],
      [48, 49, 50],
      [51, 52, 53],
      [54, 55, 56],
      [57, 58, 59],
      [60, 61, 62],
      [63]
    ] := by decide

    @[word_parts_known] lemma new_4_0_true : new 4 0 true = [
      [0, 1, 2, 3],
      [4, 5, 6, 7],
      [8, 9, 10, 11],
      [12, 13, 14, 15],
      [16, 17, 18, 19],
      [20, 21, 22, 23],
      [24, 25, 26, 27],
      [28, 29, 30, 31],
      [32, 33, 34, 35],
      [36, 37, 38, 39],
      [40, 41, 42, 43],
      [44, 45, 46, 47],
      [48, 49, 50, 51],
      [52, 53, 54, 55],
      [56, 57, 58, 59],
      [60, 61, 62, 63]
    ] := by decide

    @[word_parts_known] lemma new_4_1_true : new 4 1 true = [
      [0, 1, 2],
      [3, 4, 5, 6],
      [7, 8, 9, 10],
      [11, 12, 13, 14],
      [15, 16, 17, 18],
      [19, 20, 21, 22],
      [23, 24, 25, 26],
      [27, 28, 29, 30],
      [31, 32, 33, 34],
      [35, 36, 37, 38],
      [39, 40, 41, 42],
      [43, 44, 45, 46],
      [47, 48, 49, 50],
      [51, 52, 53, 54],
      [55, 56, 57, 58],
      [59, 60, 61, 62],
      [63]
    ] := by decide

    @[word_parts_known] lemma new_6_0_false : new 6 0 false = [
      [0, 1, 2, 3, 4, 5],
      [6, 7, 8, 9, 10, 11],
      [12, 13, 14, 15, 16, 17],
      [18, 19, 20, 21, 22, 23],
      [24, 25, 26, 27, 28, 29],
      [30, 31, 32, 33, 34, 35],
      [36, 37, 38, 39, 40, 41],
      [42, 43, 44, 45, 46, 47],
      [48, 49, 50, 51, 52, 53],
      [54, 55, 56, 57, 58, 59],
      [60, 61, 62, 63]
    ] := by decide

    @[word_parts_known] lemma new_8_0_false : new 8 0 false = [
      [0, 1, 2, 3, 4, 5, 6, 7],
      [8, 9, 10, 11, 12, 13, 14, 15],
      [16, 17, 18, 19, 20, 21, 22, 23],
      [24, 25, 26, 27, 28, 29, 30, 31],
      [32, 33, 34, 35, 36, 37, 38, 39],
      [40, 41, 42, 43, 44, 45, 46, 47],
      [48, 49, 50, 51, 52, 53, 54, 55],
      [56, 57, 58, 59, 60, 61, 62, 63]
    ] := by decide
  end WordParts

end Keccak

import Examples.Scroll.Keccak.Extraction

namespace Keccak

  lemma blinding_factors_of_meets_constraints (h: meets_constraints c): c.1.num_blinding_factors = 58 := h.2.1

  lemma fixed_of_meets_constraints (h: meets_constraints c): c.1.Fixed = fixed_func c := h.2.2.2.1


  lemma gate_0_of_meets_constraints (h: meets_constraints c): gate_0 c := h.2.2.2.2.2.2.1.1.1.1
  lemma gate_1_of_meets_constraints (h: meets_constraints c): gate_1 c := h.2.2.2.2.2.2.1.1.1.2.1
  lemma gate_2_of_meets_constraints (h: meets_constraints c): gate_2 c := h.2.2.2.2.2.2.1.1.1.2.2.1
  lemma gate_3_of_meets_constraints (h: meets_constraints c): gate_3 c := h.2.2.2.2.2.2.1.1.1.2.2.2.1
  lemma gate_4_of_meets_constraints (h: meets_constraints c): gate_4 c := h.2.2.2.2.2.2.1.1.1.2.2.2.2.1
  lemma gate_5_of_meets_constraints (h: meets_constraints c): gate_5 c := h.2.2.2.2.2.2.1.1.1.2.2.2.2.2.1
  lemma gate_6_of_meets_constraints (h: meets_constraints c): gate_6 c := h.2.2.2.2.2.2.1.1.1.2.2.2.2.2.2.1
  lemma gate_7_of_meets_constraints (h: meets_constraints c): gate_7 c := h.2.2.2.2.2.2.1.1.1.2.2.2.2.2.2.2.1
  lemma gate_8_of_meets_constraints (h: meets_constraints c): gate_8 c := h.2.2.2.2.2.2.1.1.1.2.2.2.2.2.2.2.2.1
  lemma gate_9_of_meets_constraints (h: meets_constraints c): gate_9 c := h.2.2.2.2.2.2.1.1.1.2.2.2.2.2.2.2.2.2
  lemma gate_10_of_meets_constraints (h: meets_constraints c): gate_10 c := h.2.2.2.2.2.2.1.1.2.1.1
  lemma gate_11_of_meets_constraints (h: meets_constraints c): gate_11 c := h.2.2.2.2.2.2.1.1.2.1.2.1
  lemma gate_12_of_meets_constraints (h: meets_constraints c): gate_12 c := h.2.2.2.2.2.2.1.1.2.1.2.2.1
  lemma gate_13_of_meets_constraints (h: meets_constraints c): gate_13 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.1
  lemma gate_14_of_meets_constraints (h: meets_constraints c): gate_14 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.2.1
  lemma gate_15_of_meets_constraints (h: meets_constraints c): gate_15 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.2.2.1
  lemma gate_16_of_meets_constraints (h: meets_constraints c): gate_16 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.2.2.2.1
  lemma gate_17_of_meets_constraints (h: meets_constraints c): gate_17 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.2.2.2.2.1
  lemma gate_18_of_meets_constraints (h: meets_constraints c): gate_18 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.2.2.2.2.2.1
  lemma gate_19_of_meets_constraints (h: meets_constraints c): gate_19 c := h.2.2.2.2.2.2.1.1.2.1.2.2.2.2.2.2.2.2.2
  lemma gate_20_of_meets_constraints (h: meets_constraints c): gate_20 c := h.2.2.2.2.2.2.1.1.2.2.1.1
  lemma gate_21_of_meets_constraints (h: meets_constraints c): gate_21 c := h.2.2.2.2.2.2.1.1.2.2.1.2.1
  lemma gate_22_of_meets_constraints (h: meets_constraints c): gate_22 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.1
  lemma gate_23_of_meets_constraints (h: meets_constraints c): gate_23 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.1
  lemma gate_24_of_meets_constraints (h: meets_constraints c): gate_24 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.2.1
  lemma gate_25_of_meets_constraints (h: meets_constraints c): gate_25 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.2.2.1
  lemma gate_26_of_meets_constraints (h: meets_constraints c): gate_26 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.2.2.2.1
  lemma gate_27_of_meets_constraints (h: meets_constraints c): gate_27 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.2.2.2.2.1
  lemma gate_28_of_meets_constraints (h: meets_constraints c): gate_28 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.2.2.2.2.2.1
  lemma gate_29_of_meets_constraints (h: meets_constraints c): gate_29 c := h.2.2.2.2.2.2.1.1.2.2.1.2.2.2.2.2.2.2.2.2
  lemma gate_30_of_meets_constraints (h: meets_constraints c): gate_30 c := h.2.2.2.2.2.2.1.1.2.2.2.1.1
  lemma gate_31_of_meets_constraints (h: meets_constraints c): gate_31 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.1
  lemma gate_32_of_meets_constraints (h: meets_constraints c): gate_32 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.1
  lemma gate_33_of_meets_constraints (h: meets_constraints c): gate_33 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.1
  lemma gate_34_of_meets_constraints (h: meets_constraints c): gate_34 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.2.1
  lemma gate_35_of_meets_constraints (h: meets_constraints c): gate_35 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.2.2.1
  lemma gate_36_of_meets_constraints (h: meets_constraints c): gate_36 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.2.2.2.1
  lemma gate_37_of_meets_constraints (h: meets_constraints c): gate_37 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.2.2.2.2.1
  lemma gate_38_of_meets_constraints (h: meets_constraints c): gate_38 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.2.2.2.2.2.1
  lemma gate_39_of_meets_constraints (h: meets_constraints c): gate_39 c := h.2.2.2.2.2.2.1.1.2.2.2.1.2.2.2.2.2.2.2.2.2
  lemma gate_40_of_meets_constraints (h: meets_constraints c): gate_40 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.1
  lemma gate_41_of_meets_constraints (h: meets_constraints c): gate_41 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.1
  lemma gate_42_of_meets_constraints (h: meets_constraints c): gate_42 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.1
  lemma gate_43_of_meets_constraints (h: meets_constraints c): gate_43 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.1
  lemma gate_44_of_meets_constraints (h: meets_constraints c): gate_44 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.2.1
  lemma gate_45_of_meets_constraints (h: meets_constraints c): gate_45 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.2.2.1
  lemma gate_46_of_meets_constraints (h: meets_constraints c): gate_46 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.2.2.2.1
  lemma gate_47_of_meets_constraints (h: meets_constraints c): gate_47 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.2.2.2.2.1
  lemma gate_48_of_meets_constraints (h: meets_constraints c): gate_48 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.2.2.2.2.2.1
  lemma gate_49_of_meets_constraints (h: meets_constraints c): gate_49 c := h.2.2.2.2.2.2.1.1.2.2.2.2.1.2.2.2.2.2.2.2.2.2
  lemma gate_50_of_meets_constraints (h: meets_constraints c): gate_50 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.1
  lemma gate_51_of_meets_constraints (h: meets_constraints c): gate_51 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.1
  lemma gate_52_of_meets_constraints (h: meets_constraints c): gate_52 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.1
  lemma gate_53_of_meets_constraints (h: meets_constraints c): gate_53 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.1
  lemma gate_54_of_meets_constraints (h: meets_constraints c): gate_54 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.2.1
  lemma gate_55_of_meets_constraints (h: meets_constraints c): gate_55 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.2.2.1
  lemma gate_56_of_meets_constraints (h: meets_constraints c): gate_56 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.2.2.2.1
  lemma gate_57_of_meets_constraints (h: meets_constraints c): gate_57 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.2.2.2.2.1
  lemma gate_58_of_meets_constraints (h: meets_constraints c): gate_58 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.2.2.2.2.2.1
  lemma gate_59_of_meets_constraints (h: meets_constraints c): gate_59 c := h.2.2.2.2.2.2.1.1.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2


  lemma lookup_0_of_meets_constraints (h: meets_constraints c): lookup_0 c := h.2.2.2.2.2.2.2.2.1.1.1
  lemma lookup_1_of_meets_constraints (h: meets_constraints c): lookup_1 c := h.2.2.2.2.2.2.2.2.1.1.2.1
  lemma lookup_2_of_meets_constraints (h: meets_constraints c): lookup_2 c := h.2.2.2.2.2.2.2.2.1.1.2.2.1
  lemma lookup_3_of_meets_constraints (h: meets_constraints c): lookup_3 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.1
  lemma lookup_4_of_meets_constraints (h: meets_constraints c): lookup_4 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.2.1
  lemma lookup_5_of_meets_constraints (h: meets_constraints c): lookup_5 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.1
  lemma lookup_6_of_meets_constraints (h: meets_constraints c): lookup_6 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.1
  lemma lookup_7_of_meets_constraints (h: meets_constraints c): lookup_7 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.1
  lemma lookup_8_of_meets_constraints (h: meets_constraints c): lookup_8 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.2.1
  lemma lookup_9_of_meets_constraints (h: meets_constraints c): lookup_9 c := h.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.2.2
  lemma lookup_10_of_meets_constraints (h: meets_constraints c): lookup_10 c := h.2.2.2.2.2.2.2.2.1.2.1.1
  lemma lookup_11_of_meets_constraints (h: meets_constraints c): lookup_11 c := h.2.2.2.2.2.2.2.2.1.2.1.2.1
  lemma lookup_12_of_meets_constraints (h: meets_constraints c): lookup_12 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.1
  lemma lookup_13_of_meets_constraints (h: meets_constraints c): lookup_13 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.1
  lemma lookup_14_of_meets_constraints (h: meets_constraints c): lookup_14 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.1
  lemma lookup_15_of_meets_constraints (h: meets_constraints c): lookup_15 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.1
  lemma lookup_16_of_meets_constraints (h: meets_constraints c): lookup_16 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.2.1
  lemma lookup_17_of_meets_constraints (h: meets_constraints c): lookup_17 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.2.2.1
  lemma lookup_18_of_meets_constraints (h: meets_constraints c): lookup_18 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.2.2.2.1
  lemma lookup_19_of_meets_constraints (h: meets_constraints c): lookup_19 c := h.2.2.2.2.2.2.2.2.1.2.1.2.2.2.2.2.2.2.2.2

  lemma usable_rows_range_of_meets_constraints (h: meets_constraints c): c.usable_rows ≥ 730 := h.2.2.2.2.2.1

  lemma n_range_of_meets_constraints (h: meets_constraints c): 788 < c.n := by
    have h_usable_rows := usable_rows_range_of_meets_constraints h
    have h_blinding_factors := blinding_factors_of_meets_constraints h
    unfold ValidCircuit.usable_rows at h_usable_rows
    omega

end Keccak

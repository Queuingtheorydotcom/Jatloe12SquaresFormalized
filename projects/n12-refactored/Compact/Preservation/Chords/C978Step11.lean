import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C978

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C978Step11
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C978

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (20425471/12500000)
def hi : ℚ := (164405333/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (695,radius0,radius0_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (696,radius1,radius1_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (697,radius2,radius2_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (698,radius3,radius3_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (699,radius4,radius4_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (700,radius5,radius5_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (8099,radius6,radius6_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (8100,radius7,radius7_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (8101,radius8,radius8_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (8102,radius9,radius9_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (8103,radius10,radius10_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (8104,radius11,radius11_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (8105,radius12,radius12_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (8106,radius13,radius13_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (8107,radius45,radius45_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (8108,radius46,radius46_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (8109,radius47,radius47_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (8110,radius48,radius48_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (8111,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (8112,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (8113,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (8114,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (8115,radius53,radius53_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (8116,radius54,radius54_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (8117,radius55,radius55_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (8118,radius56,radius56_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (8119,radius57,radius57_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (8120,radius58,radius58_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (8121,radius59,radius59_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (8122,radius60,radius60_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (737,radius61,radius61_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (738,radius62,radius62_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (739,radius63,radius63_checked,[.single 1, .single 6])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout978Domain1_7Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (6724,radius0,radius0_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (6725,radius1,radius1_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (6726,radius2,radius2_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (6727,radius3,radius3_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (6728,radius4,radius4_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (8131,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (8132,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (8133,radius7,radius7_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (8134,radius8,radius8_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (8135,radius9,radius9_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (8136,radius10,radius10_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (8137,radius11,radius11_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (8138,radius12,radius12_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (8139,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (8140,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (8141,radius15,radius15_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (8142,radius16,radius16_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (8143,radius17,radius17_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (8144,radius18,radius18_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (8145,radius19,radius19_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (8146,radius20,radius20_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (8147,radius21,radius21_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (8148,radius22,radius22_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (8149,radius23,radius23_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (8150,radius24,radius24_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (8151,radius25,radius25_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (8152,radius26,radius26_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (8153,radius27,radius27_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (8154,radius28,radius28_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (8155,radius30,radius30_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (8156,radius31,radius31_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (8157,radius32,radius32_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (8158,radius33,radius33_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (8159,radius34,radius34_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (8160,radius35,radius35_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (8161,radius36,radius36_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (8162,radius37,radius37_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (8163,radius38,radius38_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (8164,radius39,radius39_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (8165,radius40,radius40_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (8166,radius41,radius41_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (8167,radius42,radius42_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (8168,radius43,radius43_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (8169,radius44,radius44_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (8170,radius45,radius45_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (8171,radius46,radius46_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (8172,radius47,radius47_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (8173,radius48,radius48_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (8174,radius49,radius49_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (8175,radius50,radius50_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (8176,radius51,radius51_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (8177,radius52,radius52_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (8178,radius53,radius53_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (8179,radius54,radius54_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (8180,radius55,radius55_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (8181,radius56,radius56_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (8182,radius57,radius57_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (8183,radius58,radius58_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (8184,radius59,radius59_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (8185,radius60,radius60_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (8186,radius61,radius61_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_61 (dictionary,horizontal,lo,hi) := (8187,radius62,radius62_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_62 (dictionary,horizontal,lo,hi) := (8188,radius63,radius63_checked,[.single 2, .single 7])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53, neighbor1_54, neighbor1_55, neighbor1_56, neighbor1_57, neighbor1_58, neighbor1_59,
    neighbor1_60, neighbor1_61, neighbor1_62]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout978Domain5_8Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (8317,radius0,radius0_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (8318,radius1,radius1_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (8319,radius2,radius2_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (8320,radius3,radius3_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (8321,radius4,radius4_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (8322,radius5,radius5_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (8323,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (8324,radius7,radius7_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (8325,radius8,radius8_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (8326,radius9,radius9_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (8327,radius10,radius10_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (8328,radius11,radius11_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (8329,radius12,radius12_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (8330,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (8331,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (8332,radius15,radius15_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (8333,radius16,radius16_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (8334,radius17,radius17_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (8335,radius18,radius18_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (8336,radius19,radius19_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (8337,radius20,radius20_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (8338,radius21,radius21_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (8339,radius22,radius22_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (8340,radius23,radius23_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (8341,radius24,radius24_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (8342,radius25,radius25_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (8343,radius26,radius26_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (8344,radius27,radius27_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (8345,radius28,radius28_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (8346,radius29,radius29_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (8347,radius30,radius30_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (8348,radius31,radius31_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (8349,radius32,radius32_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (8350,radius33,radius33_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (8351,radius34,radius34_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (8352,radius39,radius39_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (8353,radius40,radius40_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (8354,radius41,radius41_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (8355,radius42,radius42_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (8356,radius43,radius43_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (8357,radius44,radius44_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (8358,radius45,radius45_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (8359,radius46,radius46_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (8360,radius47,radius47_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (8361,radius48,radius48_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (8362,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (8363,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (8364,radius51,radius51_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (8365,radius52,radius52_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (8366,radius53,radius53_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (8367,radius54,radius54_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (8368,radius55,radius55_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_52 (dictionary,horizontal,lo,hi) := (8369,radius56,radius56_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_53 (dictionary,horizontal,lo,hi) := (8370,radius57,radius57_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_54 (dictionary,horizontal,lo,hi) := (8371,radius58,radius58_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_55 (dictionary,horizontal,lo,hi) := (8372,radius59,radius59_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_56 (dictionary,horizontal,lo,hi) := (8373,radius60,radius60_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_57 (dictionary,horizontal,lo,hi) := (8374,radius61,radius61_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_58 (dictionary,horizontal,lo,hi) := (8375,radius62,radius62_checked,[.single 1, .single 8])
checked_chord_neighbor neighbor2_59 (dictionary,horizontal,lo,hi) := (8376,radius63,radius63_checked,[.single 1, .single 9])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51, neighbor2_52, neighbor2_53, neighbor2_54, neighbor2_55, neighbor2_56, neighbor2_57, neighbor2_58, neighbor2_59]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout978Domain6_11Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (7801,radius0,radius0_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(7865,[.single 1, .pair 1 2, .single 0, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (7802,radius1,radius1_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(7866,[.single 1, .pair 1 2, .single 0, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (7803,radius2,radius2_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(7867,[.single 1, .pair 1 2, .single 0, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (7804,radius3,radius3_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_keep%(7868,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (7805,radius4,radius4_checked,chord_close%(⟨[0,3],[(5,0),(1,3)]⟩),chord_keep%(7869,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (7806,radius5,radius5_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(7870,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (7807,radius6,radius6_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(7871,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (7808,radius7,radius7_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(7872,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (7809,radius8,radius8_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(7873,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (7810,radius9,radius9_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(7874,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (7811,radius10,radius10_checked,chord_close%(⟨[0,3],[(4,0),(1,3)]⟩),chord_keep%(7875,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (7812,radius11,radius11_checked,chord_close%(⟨[0,3],[(20,0),(1,3)]⟩),chord_keep%(7876,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (7813,radius12,radius12_checked,chord_close%(⟨[0,3],[(8,0),(1,3)]⟩),chord_keep%(7877,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (7814,radius13,radius13_checked,chord_close%(⟨[0,3],[(160,0),(1,3)]⟩),chord_keep%(7878,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (7815,radius14,radius14_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(7879,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (7816,radius15,radius15_checked,chord_close%(⟨[0,3],[(1,0),(8,3)]⟩),chord_keep%(7880,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (7817,radius16,radius16_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(7881,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (7818,radius17,radius17_checked,chord_close%(⟨[0,3],[(10,0),(1,3)]⟩),chord_keep%(7882,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (7819,radius18,radius18_checked,chord_close%(⟨[0,3],[(1,0),(10,3)]⟩),chord_keep%(7883,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (7820,radius19,radius19_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(7884,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 3, .single 5, .copy 12]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (7821,radius20,radius20_checked,chord_close%(⟨[0,2],[(16,0),(1,2)]⟩),chord_keep%(7885,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (7822,radius21,radius21_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(7886,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (7823,radius22,radius22_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(7887,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (7824,radius23,radius23_checked,chord_close%(⟨[0,2],[(25,0),(4,2)]⟩),chord_keep%(7888,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (7825,radius24,radius24_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(7889,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (7826,radius25,radius25_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(7890,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (7827,radius26,radius26_checked,chord_close%(⟨[0,2],[(10,0),(1,2)]⟩),chord_keep%(7891,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (7828,radius27,radius27_checked,chord_close%(⟨[0,2],[(1,0),(25,2)]⟩),chord_keep%(7892,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (7829,radius28,radius28_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(7893,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (7830,radius29,radius29_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(7894,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (7831,radius30,radius30_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(7895,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (7832,radius31,radius31_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(7896,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (7833,radius32,radius32_checked,chord_close%(⟨[0,2],[(8,0),(1,2)]⟩),chord_keep%(7897,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (7834,radius33,radius33_checked,chord_close%(⟨[0,2],[(1,0),(64,2)]⟩),chord_keep%(7898,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (7835,radius34,radius34_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(7899,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (7836,radius35,radius35_checked,chord_close%(⟨[0,2],[(1,0),(10,2)]⟩),chord_keep%(7900,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 4, .copy 12]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (7837,radius36,radius36_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(7901,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (7838,radius37,radius37_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(7902,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (7839,radius38,radius38_checked,chord_close%(⟨[0,2],[(32,0),(1,2)]⟩),chord_keep%(7903,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (7840,radius39,radius39_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(7904,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (7841,radius40,radius40_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(7905,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (7842,radius41,radius41_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(7906,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (7843,radius42,radius42_checked,chord_close%(⟨[0,2],[(1,0),(40,2)]⟩),chord_keep%(7907,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (7844,radius43,radius43_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(7908,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (7845,radius44,radius44_checked,chord_close%(⟨[0,2],[(2,0),(25,2)]⟩),chord_keep%(7909,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (7846,radius45,radius45_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(7910,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (7847,radius46,radius46_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(7911,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (7848,radius47,radius47_checked,chord_close%(⟨[0,2],[(1,0),(10,2)]⟩),chord_keep%(7912,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (7849,radius48,radius48_checked,chord_close%(⟨[0,2],[(8,0),(5,2)]⟩),chord_keep%(7913,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (7850,radius49,radius49_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(7914,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (7851,radius50,radius50_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(7915,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (7852,radius51,radius51_checked,chord_close%(⟨[0,2],[(1,0),(25,2)]⟩),chord_keep%(7916,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (7853,radius52,radius52_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(7917,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (7854,radius53,radius53_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(7918,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (7855,radius54,radius54_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(7919,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (7856,radius55,radius55_checked,chord_close%(⟨[0,2],[(1,0),(20,2)]⟩),chord_keep%(7920,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (7857,radius56,radius56_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(7921,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (7858,radius57,radius57_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(7922,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (7859,radius58,radius58_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_keep%(7923,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (7860,radius59,radius59_checked,chord_close%(⟨[0,2],[(5,0),(128,2)]⟩),chord_keep%(7924,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (7861,radius60,radius60_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(7925,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (7862,radius61,radius61_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(7926,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (7863,radius62,radius62_checked,chord_close%(⟨[0,2],[(5,0),(4,2)]⟩),chord_keep%(7927,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (7864,radius63,radius63_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(7928,[.pair 1 5, .single 0, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 0, .single 7, .copy 14]))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53, plan54, plan55, plan56, plan57, plan58, plan59,
    plan60, plan61, plan62, plan63]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout978Domain10_0Ids := by rfl
def outputIds : List (Fin poseCount) := [7865,7866,7867,7868,7869,7870,7871,7872,7873,7874,7875,7876,7877,7878,7879,7880,7881,7882,7883,7884,7885,7886,7887,7888,7889,7890,7891,7892,7893,7894,7895,7896,7897,7898,7899,7900,7901,7902,7903,7904,7905,7906,7907,7908,7909,7910,7911,7912,7913,7914,7915,7916,7917,7918,7919,7920,7921,7922,7923,7924,7925,7926,7927,7928]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout978Domain10_12Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout978Domain10_12Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout978Domain10_0 (q 0))
    (h0 : OrientedPoseCovered continuousScout978Domain1_7 (q 1))
    (h1 : OrientedPoseCovered continuousScout978Domain5_8 (q 2))
    (h2 : OrientedPoseCovered continuousScout978Domain6_11 (q 3))
    : OrientedPoseCovered continuousScout978Domain10_12 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout978Domain10_0Ids continuousScout978Domain10_12Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout978Domain1_7Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout978Domain5_8Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout978Domain6_11Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![16384,2,256,512]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout978Domain10_0 (p.square (ownerIndex p 16384)))
    (h0 : OrientedPoseCovered continuousScout978Domain1_7 (p.square (ownerIndex p 2)))
    (h1 : OrientedPoseCovered continuousScout978Domain5_8 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout978Domain6_11 (p.square (ownerIndex p 512)))
    : OrientedPoseCovered continuousScout978Domain10_12 (p.square (ownerIndex p 16384)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout978Domain10_0 continuousScout978Domain10_12
    ![continuousScout978Domain1_7,continuousScout978Domain5_8,continuousScout978Domain6_11]
    (fun q side box disjoint source neighbors =>
      sound q side box disjoint source (neighbors 0) (neighbors 1) (neighbors 2))
    p family_exact incoming
  intro i; fin_cases i
  · exact h0
  · exact h1
  · exact h2

#print axioms packing_sound

#print axioms sound

end
end N12Compact.Preservation.Chords.C978Step11

import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C973

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C973Step25
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C973

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (145605219/100000000)
def hi : ℚ := (153618673/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (577,radius0,radius0_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (6378,radius1,radius1_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (6379,radius2,radius2_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (6380,radius3,radius3_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (6381,radius4,radius4_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (582,radius5,radius5_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (583,radius6,radius6_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (584,radius7,radius7_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (6382,radius8,radius8_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (6383,radius9,radius9_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (6384,radius10,radius10_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (6385,radius11,radius11_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (6386,radius12,radius12_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (6387,radius13,radius13_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (6388,radius14,radius14_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (6389,radius15,radius15_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (6390,radius16,radius16_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (6391,radius17,radius17_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (6392,radius18,radius18_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (6393,radius19,radius19_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (6394,radius20,radius20_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (6395,radius21,radius21_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (6396,radius22,radius22_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (6397,radius23,radius23_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (6398,radius24,radius24_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (6399,radius25,radius25_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (6400,radius26,radius26_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (6401,radius27,radius27_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (605,radius28,radius28_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (606,radius29,radius29_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (6402,radius30,radius30_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (6403,radius31,radius31_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (6404,radius32,radius32_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (6405,radius33,radius33_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (6406,radius34,radius34_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (6407,radius35,radius35_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (6408,radius36,radius36_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (6409,radius37,radius37_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (6410,radius38,radius38_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (6411,radius39,radius39_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (6412,radius40,radius40_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (6413,radius41,radius41_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (6414,radius42,radius42_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (6415,radius43,radius43_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (6416,radius44,radius44_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_45 (dictionary,horizontal,lo,hi) := (6417,radius45,radius45_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_46 (dictionary,horizontal,lo,hi) := (6418,radius46,radius46_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_47 (dictionary,horizontal,lo,hi) := (6419,radius47,radius47_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_48 (dictionary,horizontal,lo,hi) := (6420,radius48,radius48_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_49 (dictionary,horizontal,lo,hi) := (6421,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_50 (dictionary,horizontal,lo,hi) := (6422,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_51 (dictionary,horizontal,lo,hi) := (6423,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_52 (dictionary,horizontal,lo,hi) := (6424,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_53 (dictionary,horizontal,lo,hi) := (6425,radius53,radius53_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_54 (dictionary,horizontal,lo,hi) := (6426,radius54,radius54_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_55 (dictionary,horizontal,lo,hi) := (6427,radius55,radius55_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_56 (dictionary,horizontal,lo,hi) := (6428,radius56,radius56_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_57 (dictionary,horizontal,lo,hi) := (6429,radius57,radius57_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_58 (dictionary,horizontal,lo,hi) := (635,radius58,radius58_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_59 (dictionary,horizontal,lo,hi) := (636,radius59,radius59_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_60 (dictionary,horizontal,lo,hi) := (637,radius60,radius60_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_61 (dictionary,horizontal,lo,hi) := (638,radius61,radius61_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_62 (dictionary,horizontal,lo,hi) := (639,radius62,radius62_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_63 (dictionary,horizontal,lo,hi) := (640,radius63,radius63_checked,[.single 1, .single 6])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44, neighbor0_45, neighbor0_46, neighbor0_47,
    neighbor0_48, neighbor0_49, neighbor0_50, neighbor0_51, neighbor0_52, neighbor0_53, neighbor0_54, neighbor0_55, neighbor0_56, neighbor0_57, neighbor0_58, neighbor0_59,
    neighbor0_60, neighbor0_61, neighbor0_62, neighbor0_63]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout973Domain1_20Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (6850,radius0,radius0_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (6851,radius1,radius1_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (6852,radius2,radius2_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (6853,radius3,radius3_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (6854,radius4,radius4_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (6855,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (6856,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (6857,radius7,radius7_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (6858,radius8,radius8_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (6859,radius9,radius9_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (6860,radius10,radius10_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (6861,radius11,radius11_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (6862,radius12,radius12_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (6863,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (6864,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (6865,radius15,radius15_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (6866,radius16,radius16_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (6867,radius17,radius17_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (6868,radius20,radius20_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (6869,radius40,radius40_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (6870,radius41,radius41_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (6871,radius42,radius42_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (6872,radius43,radius43_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (6873,radius44,radius44_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (6874,radius45,radius45_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (6875,radius46,radius46_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (6876,radius47,radius47_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (6877,radius48,radius48_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (6878,radius49,radius49_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (6879,radius50,radius50_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (6880,radius51,radius51_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (6881,radius52,radius52_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (6882,radius53,radius53_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (6883,radius54,radius54_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (6884,radius55,radius55_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (6885,radius56,radius56_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (6886,radius57,radius57_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (6887,radius58,radius58_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (6888,radius59,radius59_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (6889,radius60,radius60_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (6890,radius61,radius61_checked,[.single 3, .single 6])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (6891,radius62,radius62_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (6892,radius63,radius63_checked,[.single 2, .single 5])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout973Domain5_22Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (7021,radius0,radius0_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (7022,radius1,radius1_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (7023,radius2,radius2_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (7024,radius3,radius3_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (7025,radius4,radius4_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (7026,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (7027,radius61,radius61_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (7028,radius62,radius62_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (7029,radius63,radius63_checked,[.single 2, .single 7])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout973Domain6_24Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (6094,radius0,radius0_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (6095,radius1,radius1_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6139,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (6096,radius2,radius2_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (6097,radius3,radius3_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_close%(⟨[0,6],[(16,0),(1,6)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (6098,radius4,radius4_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,6],[(1,0),(128,6)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (6099,radius5,radius5_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,6],[(25,0),(1,6)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (6100,radius6,radius6_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,6],[(2,0),(1,6)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (6101,radius7,radius7_checked,chord_close%(⟨[0,2],[(1,0),(16,2)]⟩),chord_close%(⟨[0,6],[(1,0),(10,6)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (6102,radius8,radius8_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,6],[(1,0),(10,6)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (6103,radius9,radius9_checked,chord_close%(⟨[0,2],[(8,0),(1,2)]⟩),chord_close%(⟨[0,5],[(1,0),(4,5)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (6104,radius10,radius10_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (6105,radius11,radius11_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (6106,radius12,radius12_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_close%(⟨[0,5],[(1,0),(8,5)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (6107,radius13,radius13_checked,chord_close%(⟨[0,2],[(1,0),(80,2)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (6108,radius14,radius14_checked,chord_close%(⟨[0,2],[(20,0),(1,2)]⟩),chord_keep%(6140,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (6109,radius15,radius15_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(6141,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (6110,radius16,radius16_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6142,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (6111,radius17,radius17_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6143,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (6112,radius18,radius18_checked,chord_close%(⟨[0,2],[(16,0),(1,2)]⟩),chord_keep%(6144,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (6113,radius19,radius19_checked,chord_close%(⟨[0,2],[(8,0),(5,2)]⟩),chord_keep%(6145,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (6114,radius20,radius20_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6146,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (6115,radius21,radius21_checked,chord_close%(⟨[0,2],[(80,0),(1,2)]⟩),chord_keep%(6147,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (6116,radius22,radius22_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6148,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (6117,radius23,radius23_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6149,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (6118,radius24,radius24_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(6150,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (6119,radius25,radius25_checked,chord_close%(⟨[0,2],[(32,0),(1,2)]⟩),chord_keep%(6151,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (6120,radius26,radius26_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(6152,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (6121,radius27,radius27_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(6153,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (6122,radius28,radius28_checked,chord_close%(⟨[0,2],[(1,0),(10,2)]⟩),chord_keep%(6154,[.pair 1 4, .single 0, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (6123,radius29,radius29_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6155,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (6124,radius30,radius30_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(6156,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 2, .single 4, .copy 11]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (6125,radius50,radius50_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_close%(⟨[0,4],[(8,0),(1,4)]⟩))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (6126,radius51,radius51_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (6127,radius52,radius52_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_close%(⟨[0,4],[(50,0),(1,4)]⟩))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (6128,radius53,radius53_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (6129,radius54,radius54_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,4],[(5,0),(4,4)]⟩))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (6130,radius55,radius55_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(6157,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (6131,radius56,radius56_checked,chord_close%(⟨[0,2],[(1,0),(16,2)]⟩),chord_keep%(6158,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (6132,radius57,radius57_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(6159,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (6133,radius58,radius58_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6160,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (6134,radius59,radius59_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(6161,[.single 0, .single 3, .single 4, .pair 3 5, .pair 0 5, .pair 0 5, .single 3, .single 0, .single 4, .copy 11]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (6135,radius60,radius60_checked,chord_close%(⟨[0,3],[(16,0),(5,3)]⟩),chord_keep%(6162,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (6136,radius61,radius61_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(6163,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (6137,radius62,radius62_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (6138,radius63,radius63_checked,chord_close%(⟨[0,3],[(1,0),(25,3)]⟩),chord_close%(⟨[0,5],[(5,0),(1,5)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout973Domain10_17Ids := by rfl
def outputIds : List (Fin poseCount) := [6139,6140,6141,6142,6143,6144,6145,6146,6147,6148,6149,6150,6151,6152,6153,6154,6155,6156,6157,6158,6159,6160,6161,6162,6163]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout973Domain10_26Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout973Domain10_26Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout973Domain10_17 (q 0))
    (h0 : OrientedPoseCovered continuousScout973Domain1_20 (q 1))
    (h1 : OrientedPoseCovered continuousScout973Domain5_22 (q 2))
    (h2 : OrientedPoseCovered continuousScout973Domain6_24 (q 3))
    : OrientedPoseCovered continuousScout973Domain10_26 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout973Domain10_17Ids continuousScout973Domain10_26Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain1_20Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain5_22Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain6_24Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![16384,2,256,512]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout973Domain10_17 (p.square (ownerIndex p 16384)))
    (h0 : OrientedPoseCovered continuousScout973Domain1_20 (p.square (ownerIndex p 2)))
    (h1 : OrientedPoseCovered continuousScout973Domain5_22 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout973Domain6_24 (p.square (ownerIndex p 512)))
    : OrientedPoseCovered continuousScout973Domain10_26 (p.square (ownerIndex p 16384)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout973Domain10_17 continuousScout973Domain10_26
    ![continuousScout973Domain1_20,continuousScout973Domain5_22,continuousScout973Domain6_24]
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
end N12Compact.Preservation.Chords.C973Step25

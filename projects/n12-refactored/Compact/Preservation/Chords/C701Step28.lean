import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C701

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C701Step28
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C701

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (154025979/50000000)
def hi : ℚ := (63250131/20000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (854,radius0,radius0_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (855,radius1,radius1_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (856,radius2,radius2_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (857,radius3,radius3_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (858,radius4,radius4_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (859,radius5,radius5_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (860,radius6,radius6_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (861,radius7,radius7_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (862,radius8,radius8_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (863,radius48,radius48_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (864,radius49,radius49_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (865,radius50,radius50_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (866,radius51,radius51_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (867,radius52,radius52_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (868,radius53,radius53_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (869,radius54,radius54_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (870,radius55,radius55_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (871,radius56,radius56_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (872,radius57,radius57_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (873,radius58,radius58_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (874,radius59,radius59_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (875,radius60,radius60_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (876,radius61,radius61_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (877,radius62,radius62_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (878,radius63,radius63_checked,[.single 5, .single 1])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout701Domain2_5Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (1102,radius0,radius0_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (1103,radius1,radius1_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (1104,radius2,radius2_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (1105,radius3,radius3_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (1106,radius4,radius4_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (1107,radius5,radius5_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (1108,radius6,radius6_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (1109,radius7,radius7_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (1110,radius8,radius8_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (1111,radius9,radius9_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (1112,radius12,radius12_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (1113,radius13,radius13_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (1114,radius14,radius14_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (1115,radius15,radius15_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (1116,radius16,radius16_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (1117,radius17,radius17_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (1118,radius18,radius18_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (1119,radius19,radius19_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (1120,radius59,radius59_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (1121,radius60,radius60_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (1122,radius61,radius61_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (1123,radius62,radius62_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (1124,radius63,radius63_checked,[.single 7, .single 3])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout701Domain4_23Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (262,radius0,radius0_checked,[.single 8, .single 5])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (263,radius1,radius1_checked,[.single 8, .single 5])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (264,radius2,radius2_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (265,radius3,radius3_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (266,radius4,radius4_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (267,radius5,radius5_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (268,radius6,radius6_checked,[.single 8, .single 5])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (269,radius7,radius7_checked,[.single 8, .single 5])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (270,radius8,radius8_checked,[.single 8, .single 5])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (271,radius9,radius9_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (272,radius10,radius10_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (273,radius11,radius11_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (274,radius12,radius12_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (275,radius13,radius13_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (276,radius14,radius14_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (277,radius15,radius15_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (278,radius16,radius16_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (279,radius17,radius17_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (280,radius18,radius18_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (281,radius19,radius19_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (282,radius20,radius20_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (283,radius21,radius21_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (284,radius34,radius34_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (285,radius35,radius35_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (286,radius36,radius36_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (287,radius37,radius37_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (288,radius38,radius38_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (289,radius39,radius39_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (290,radius40,radius40_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (291,radius41,radius41_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (292,radius42,radius42_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (293,radius43,radius43_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (294,radius44,radius44_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (295,radius45,radius45_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (296,radius46,radius46_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (297,radius47,radius47_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (298,radius48,radius48_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (299,radius49,radius49_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (300,radius50,radius50_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (301,radius51,radius51_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (302,radius52,radius52_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (303,radius53,radius53_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (304,radius54,radius54_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (305,radius55,radius55_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (306,radius56,radius56_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (307,radius57,radius57_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (308,radius58,radius58_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (309,radius59,radius59_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (310,radius60,radius60_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (311,radius61,radius61_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (312,radius62,radius62_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (313,radius63,radius63_checked,[.single 6, .single 2])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout701Domain10_6Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (879,radius0,radius0_checked,chord_keep%(943,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .single 7, .single 8, .single 8, .single 0, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (880,radius1,radius1_checked,chord_keep%(944,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .single 7, .single 8, .single 8, .single 0, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(2,0),(1,5)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (881,radius2,radius2_checked,chord_keep%(945,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (882,radius3,radius3_checked,chord_keep%(946,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (883,radius4,radius4_checked,chord_keep%(947,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(128,0),(1,5)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (884,radius5,radius5_checked,chord_keep%(948,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(10,5)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (885,radius6,radius6_checked,chord_keep%(949,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(10,0),(1,5)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (886,radius7,radius7_checked,chord_keep%(950,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(10,5)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (887,radius8,radius8_checked,chord_keep%(951,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(5,0),(4,5)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (888,radius9,radius9_checked,chord_keep%(952,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(5,5)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (889,radius10,radius10_checked,chord_keep%(953,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (890,radius11,radius11_checked,chord_keep%(954,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (891,radius12,radius12_checked,chord_keep%(955,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]),chord_close%(⟨[0,4],[(5,0),(2,4)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (892,radius13,radius13_checked,chord_keep%(956,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (893,radius14,radius14_checked,chord_keep%(957,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (894,radius15,radius15_checked,chord_keep%(958,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (895,radius16,radius16_checked,chord_keep%(959,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (896,radius17,radius17_checked,chord_keep%(960,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (897,radius18,radius18_checked,chord_keep%(961,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (898,radius19,radius19_checked,chord_keep%(962,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (899,radius20,radius20_checked,chord_keep%(963,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (900,radius21,radius21_checked,chord_keep%(964,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (901,radius22,radius22_checked,chord_keep%(965,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (902,radius23,radius23_checked,chord_keep%(966,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (903,radius24,radius24_checked,chord_keep%(967,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (904,radius25,radius25_checked,chord_keep%(968,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (905,radius26,radius26_checked,chord_keep%(969,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (906,radius27,radius27_checked,chord_keep%(970,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (907,radius28,radius28_checked,chord_keep%(971,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (908,radius29,radius29_checked,chord_keep%(972,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(625,0),(1,4)]⟩))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (909,radius30,radius30_checked,chord_keep%(973,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(4,0),(1,4)]⟩))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (910,radius31,radius31_checked,chord_keep%(974,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (911,radius32,radius32_checked,chord_keep%(975,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (912,radius33,radius33_checked,chord_keep%(976,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (913,radius34,radius34_checked,chord_keep%(977,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (914,radius35,radius35_checked,chord_keep%(978,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(16,0),(1,4)]⟩))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (915,radius36,radius36_checked,chord_keep%(979,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (916,radius37,radius37_checked,chord_keep%(980,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(50,0),(1,4)]⟩))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (917,radius38,radius38_checked,chord_keep%(981,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(5,0),(4,4)]⟩))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (918,radius39,radius39_checked,chord_keep%(982,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 4, .single 2, .single 5, .copy 11]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (919,radius40,radius40_checked,chord_keep%(983,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (920,radius41,radius41_checked,chord_keep%(984,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (921,radius42,radius42_checked,chord_keep%(985,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (922,radius43,radius43_checked,chord_keep%(986,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (923,radius44,radius44_checked,chord_keep%(987,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (924,radius45,radius45_checked,chord_keep%(988,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (925,radius46,radius46_checked,chord_keep%(989,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (926,radius47,radius47_checked,chord_keep%(990,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(16,0),(1,4)]⟩))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (927,radius48,radius48_checked,chord_keep%(991,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(5,0),(4,4)]⟩))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (928,radius49,radius49_checked,chord_keep%(992,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (929,radius50,radius50_checked,chord_keep%(993,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (930,radius51,radius51_checked,chord_keep%(994,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (931,radius52,radius52_checked,chord_keep%(995,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(8,0),(1,4)]⟩))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (932,radius53,radius53_checked,chord_keep%(996,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (933,radius54,radius54_checked,chord_keep%(997,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(1,0),(10,4)]⟩))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (934,radius55,radius55_checked,chord_keep%(998,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (935,radius56,radius56_checked,chord_keep%(999,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(20,0),(1,5)]⟩))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (936,radius57,radius57_checked,chord_keep%(1000,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (937,radius58,radius58_checked,chord_keep%(1001,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(1,0),(4,5)]⟩))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (938,radius59,radius59_checked,chord_keep%(1002,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(1,0),(4,5)]⟩))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (939,radius60,radius60_checked,chord_keep%(1003,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(25,0),(1,5)]⟩))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (940,radius61,radius61_checked,chord_keep%(1004,[.single 1, .single 2, .pair 1 3, .single 0, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(8,0),(1,5)]⟩))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (941,radius62,radius62_checked,chord_keep%(1005,[.single 1, .single 2, .pair 1 3, .single 0, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(1,0),(16,5)]⟩))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (942,radius63,radius63_checked,chord_keep%(1006,[.single 1, .single 2, .pair 1 3, .single 0, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,5],[(1,0),(5,5)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53, plan54, plan55, plan56, plan57, plan58, plan59,
    plan60, plan61, plan62, plan63]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout701Domain3_0Ids := by rfl
def outputIds : List (Fin poseCount) := [943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout701Domain3_29Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout701Domain3_29Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout701Domain3_0 (q 0))
    (h0 : OrientedPoseCovered continuousScout701Domain2_5 (q 1))
    (h1 : OrientedPoseCovered continuousScout701Domain4_23 (q 2))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (q 3))
    : OrientedPoseCovered continuousScout701Domain3_29 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout701Domain3_0Ids continuousScout701Domain3_29Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain2_5Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain4_23Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain10_6Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![16,12,32,16384]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout701Domain3_0 (p.square (ownerIndex p 16)))
    (h0 : OrientedPoseCovered continuousScout701Domain2_5 (p.square (ownerIndex p 12)))
    (h1 : OrientedPoseCovered continuousScout701Domain4_23 (p.square (ownerIndex p 32)))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)))
    : OrientedPoseCovered continuousScout701Domain3_29 (p.square (ownerIndex p 16)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout701Domain3_0 continuousScout701Domain3_29
    ![continuousScout701Domain2_5,continuousScout701Domain4_23,continuousScout701Domain10_6]
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
end N12Compact.Preservation.Chords.C701Step28

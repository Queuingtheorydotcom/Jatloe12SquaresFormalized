import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C701

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C701Step06
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C701

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (159907879/100000000)
def hi : ℚ := (32301159/20000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (695,radius0,radius0_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (696,radius1,radius1_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (697,radius2,radius2_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (698,radius3,radius3_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (699,radius4,radius4_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (700,radius5,radius5_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (701,radius6,radius6_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (702,radius7,radius7_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (703,radius8,radius8_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (704,radius9,radius9_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (705,radius10,radius10_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (706,radius11,radius11_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (707,radius12,radius12_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (708,radius13,radius13_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (709,radius33,radius33_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (710,radius34,radius34_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (711,radius35,radius35_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (712,radius36,radius36_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (713,radius37,radius37_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (714,radius38,radius38_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (715,radius39,radius39_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (716,radius40,radius40_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (717,radius41,radius41_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (718,radius42,radius42_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (719,radius43,radius43_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (720,radius44,radius44_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (721,radius45,radius45_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (722,radius46,radius46_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (723,radius47,radius47_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (724,radius48,radius48_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (725,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (726,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (727,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (728,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (729,radius53,radius53_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (730,radius54,radius54_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (731,radius55,radius55_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (732,radius56,radius56_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (733,radius57,radius57_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (734,radius58,radius58_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (735,radius59,radius59_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (736,radius60,radius60_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (737,radius61,radius61_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (738,radius62,radius62_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (739,radius63,radius63_checked,[.single 1, .single 6])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout701Domain1_3Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (1189,radius0,radius0_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (1190,radius1,radius1_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (1191,radius2,radius2_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (1192,radius3,radius3_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (1193,radius4,radius4_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (1194,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (1195,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (1196,radius7,radius7_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (1197,radius8,radius8_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (1198,radius9,radius9_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (1199,radius10,radius10_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (1200,radius11,radius11_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (1201,radius12,radius12_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (1202,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (1203,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (1204,radius15,radius15_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (1205,radius16,radius16_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (1206,radius17,radius17_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (1207,radius18,radius18_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (1208,radius19,radius19_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (1209,radius20,radius20_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (1210,radius21,radius21_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (1211,radius22,radius22_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (1212,radius23,radius23_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (1213,radius24,radius24_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (1214,radius25,radius25_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (1215,radius26,radius26_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (1216,radius27,radius27_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (1217,radius28,radius28_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (1218,radius29,radius29_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (1219,radius30,radius30_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (1220,radius31,radius31_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (1221,radius32,radius32_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (1222,radius33,radius33_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (1223,radius34,radius34_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (1224,radius35,radius35_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (1225,radius36,radius36_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (1226,radius37,radius37_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (1227,radius38,radius38_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (1228,radius39,radius39_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (1229,radius40,radius40_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (1230,radius41,radius41_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (1231,radius42,radius42_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (1232,radius43,radius43_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (1233,radius44,radius44_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (1234,radius45,radius45_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (1235,radius46,radius46_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (1236,radius47,radius47_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (1237,radius48,radius48_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (1238,radius49,radius49_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (1239,radius50,radius50_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (1240,radius51,radius51_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (1241,radius52,radius52_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (1242,radius53,radius53_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (1243,radius54,radius54_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (1244,radius55,radius55_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (1245,radius56,radius56_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (1246,radius57,radius57_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (1247,radius58,radius58_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (1248,radius59,radius59_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (1249,radius60,radius60_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_61 (dictionary,horizontal,lo,hi) := (1250,radius61,radius61_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_62 (dictionary,horizontal,lo,hi) := (1251,radius62,radius62_checked,[.single 2, .single 8])
checked_chord_neighbor neighbor1_63 (dictionary,horizontal,lo,hi) := (1252,radius63,radius63_checked,[.single 2, .single 8])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53, neighbor1_54, neighbor1_55, neighbor1_56, neighbor1_57, neighbor1_58, neighbor1_59,
    neighbor1_60, neighbor1_61, neighbor1_62, neighbor1_63]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout701Domain6_0Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (262,radius0,radius0_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (263,radius1,radius1_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (264,radius2,radius2_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (265,radius3,radius3_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (266,radius4,radius4_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (267,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (268,radius6,radius6_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (269,radius7,radius7_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (270,radius8,radius8_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (271,radius9,radius9_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (272,radius10,radius10_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (273,radius11,radius11_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (274,radius12,radius12_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (275,radius13,radius13_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (276,radius14,radius14_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (277,radius15,radius15_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (278,radius16,radius16_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (279,radius17,radius17_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (280,radius18,radius18_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (281,radius19,radius19_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (282,radius20,radius20_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (283,radius21,radius21_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (284,radius34,radius34_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (285,radius35,radius35_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (286,radius36,radius36_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (287,radius37,radius37_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (288,radius38,radius38_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (289,radius39,radius39_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (290,radius40,radius40_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (291,radius41,radius41_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (292,radius42,radius42_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (293,radius43,radius43_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (294,radius44,radius44_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (295,radius45,radius45_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (296,radius46,radius46_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (297,radius47,radius47_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (298,radius48,radius48_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (299,radius49,radius49_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (300,radius50,radius50_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (301,radius51,radius51_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (302,radius52,radius52_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (303,radius53,radius53_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (304,radius54,radius54_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (305,radius55,radius55_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (306,radius56,radius56_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (307,radius57,radius57_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (308,radius58,radius58_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (309,radius59,radius59_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (310,radius60,radius60_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (311,radius61,radius61_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (312,radius62,radius62_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (313,radius63,radius63_checked,[.single 1, .single 4])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout701Domain10_6Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (1400,radius0,radius0_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1473,[.pair 1 7, .single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .pair 0 6, .single 0, .single 7, .copy 14]))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (1401,radius1,radius1_checked,chord_close%(⟨[0,2],[(8,0),(1,2)]⟩),chord_keep%(1474,[.pair 1 7, .single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .pair 0 6, .single 0, .single 7, .copy 14]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (1402,radius2,radius2_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(1475,[.pair 1 7, .single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .pair 0 6, .single 0, .single 7, .copy 14]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (1403,radius3,radius3_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(1476,[.pair 1 6, .single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .pair 0 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (1404,radius4,radius4_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(1477,[.pair 1 7, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 0, .single 7, .copy 14]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (1405,radius5,radius5_checked,chord_close%(⟨[0,2],[(1,0),(20,2)]⟩),chord_keep%(1478,[.pair 1 7, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 0, .single 7, .copy 14]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (1406,radius6,radius6_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(1479,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (1407,radius7,radius7_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(1480,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (1408,radius8,radius8_checked,chord_close%(⟨[0,2],[(1,0),(64,2)]⟩),chord_keep%(1481,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (1409,radius9,radius9_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(1482,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (1410,radius10,radius10_checked,chord_close%(⟨[0,2],[(1,0),(25,2)]⟩),chord_keep%(1483,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (1411,radius11,radius11_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(1484,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (1412,radius12,radius12_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1485,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (1413,radius13,radius13_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1486,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (1414,radius14,radius14_checked,chord_close%(⟨[0,2],[(50,0),(1,2)]⟩),chord_keep%(1487,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (1415,radius15,radius15_checked,chord_close%(⟨[0,2],[(1,0),(10,2)]⟩),chord_keep%(1488,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (1416,radius16,radius16_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(1489,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (1417,radius17,radius17_checked,chord_close%(⟨[0,3],[(1,0),(2,3)]⟩),chord_keep%(1490,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 5, .single 3, .single 8, .copy 15]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (1418,radius18,radius18_checked,chord_close%(⟨[0,2],[(4,0),(25,2)]⟩),chord_keep%(1491,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (1419,radius19,radius19_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(1492,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (1420,radius20,radius20_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(1493,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (1421,radius21,radius21_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(1494,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (1422,radius22,radius22_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1495,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (1423,radius23,radius23_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(1496,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (1424,radius24,radius24_checked,chord_close%(⟨[0,2],[(160,0),(1,2)]⟩),chord_keep%(1497,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (1425,radius25,radius25_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(1498,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (1426,radius26,radius26_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(1499,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 7, .copy 15]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (1427,radius27,radius27_checked,chord_close%(⟨[0,2],[(4,0),(5,2)]⟩),chord_keep%(1500,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (1428,radius28,radius28_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(1501,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 11, .single 11, .single 5, .single 3, .single 8, .copy 16]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (1429,radius29,radius29_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(1502,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 11, .single 11, .single 5, .single 3, .single 9, .copy 16]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (1430,radius30,radius30_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_keep%(1503,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 11, .single 11, .single 5, .single 3, .single 9, .copy 16]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (1431,radius31,radius31_checked,chord_close%(⟨[0,3],[(25,0),(8,3)]⟩),chord_keep%(1504,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 11, .single 11, .single 5, .single 3, .single 9, .copy 16]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (1432,radius32,radius32_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(1505,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 11, .single 11, .single 5, .single 3, .single 9, .copy 16]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (1433,radius33,radius33_checked,chord_close%(⟨[0,3],[(5,0),(1,3)]⟩),chord_keep%(1506,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 11, .single 11, .single 5, .single 3, .single 9, .copy 16]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (1434,radius34,radius34_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(1507,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (1435,radius35,radius35_checked,chord_close%(⟨[0,2],[(5,0),(4,2)]⟩),chord_keep%(1508,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (1436,radius36,radius36_checked,chord_close%(⟨[0,2],[(25,0),(1,2)]⟩),chord_keep%(1509,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (1437,radius37,radius37_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(1510,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (1438,radius38,radius38_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(1511,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (1439,radius39,radius39_checked,chord_close%(⟨[0,2],[(1,0),(40,2)]⟩),chord_keep%(1512,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (1440,radius40,radius40_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(1513,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (1441,radius41,radius41_checked,chord_close%(⟨[0,2],[(1,0),(128,2)]⟩),chord_keep%(1514,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (1442,radius42,radius42_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(1515,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (1443,radius43,radius43_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(1516,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (1444,radius44,radius44_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(1517,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (1445,radius45,radius45_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1518,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (1446,radius46,radius46_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(1519,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (1447,radius47,radius47_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(1520,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (1448,radius48,radius48_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(1521,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (1449,radius49,radius49_checked,chord_close%(⟨[0,2],[(1,0),(40,2)]⟩),chord_keep%(1522,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (1450,radius50,radius50_checked,chord_close%(⟨[0,2],[(8,0),(1,2)]⟩),chord_keep%(1523,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (1451,radius56,radius56_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_close%(⟨[0,6],[(10,0),(1,6)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (1452,radius63,radius63_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(1524,[.single 0, .pair 4 5, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 5, .single 0, .single 7, .copy 14]))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout701Domain7_0Ids := by rfl
def outputIds : List (Fin poseCount) := [1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491,1492,1493,1494,1495,1496,1497,1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout701Domain7_7Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout701Domain7_7Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout701Domain7_0 (q 0))
    (h0 : OrientedPoseCovered continuousScout701Domain1_3 (q 1))
    (h1 : OrientedPoseCovered continuousScout701Domain6_0 (q 2))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (q 3))
    : OrientedPoseCovered continuousScout701Domain7_7 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout701Domain7_0Ids continuousScout701Domain7_7Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain1_3Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain6_0Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain10_6Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![1536,2,256,16384]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout701Domain7_0 (p.square (ownerIndex p 1536)))
    (h0 : OrientedPoseCovered continuousScout701Domain1_3 (p.square (ownerIndex p 2)))
    (h1 : OrientedPoseCovered continuousScout701Domain6_0 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)))
    : OrientedPoseCovered continuousScout701Domain7_7 (p.square (ownerIndex p 1536)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout701Domain7_0 continuousScout701Domain7_7
    ![continuousScout701Domain1_3,continuousScout701Domain6_0,continuousScout701Domain10_6]
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
end N12Compact.Preservation.Chords.C701Step06

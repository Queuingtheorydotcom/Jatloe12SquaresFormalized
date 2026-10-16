import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C701

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C701Step14
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C701

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (73412811/50000000)
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

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (1390,radius0,radius0_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (1391,radius1,radius1_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (1392,radius2,radius2_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (1393,radius3,radius3_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (1394,radius4,radius4_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (1395,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (1396,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (1397,radius61,radius61_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (1398,radius62,radius62_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (1399,radius63,radius63_checked,[.single 2, .single 6])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout701Domain6_13Ids := by rfl

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

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (1716,radius0,radius0_checked,chord_keep%(1775,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (1717,radius1,radius1_checked,chord_keep%(1776,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (1718,radius2,radius2_checked,chord_keep%(1777,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(5,0),(4,5)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (1719,radius3,radius3_checked,chord_keep%(1778,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(2,0),(1,5)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (1720,radius4,radius4_checked,chord_keep%(1779,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(4,0),(1,5)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (1721,radius5,radius5_checked,chord_keep%(1780,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(1,0),(8,5)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (1722,radius6,radius6_checked,chord_keep%(1781,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(40,0),(1,5)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (1723,radius7,radius7_checked,chord_keep%(1782,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(1,0),(20,5)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (1724,radius8,radius8_checked,chord_keep%(1783,[.pair 1 2, .single 2, .single 3, .pair 2 4, .single 0, .pair 0 1, .pair 0 1, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(5,0),(1,5)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (1725,radius9,radius9_checked,chord_keep%(1784,[.single 1, .single 2, .single 3, .pair 2 4, .single 0, .pair 1 6, .single 7, .single 7, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (1726,radius10,radius10_checked,chord_keep%(1785,[.single 1, .single 2, .single 3, .pair 2 4, .single 0, .pair 1 6, .single 7, .single 7, .single 3, .single 2, .single 0, .copy 12]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (1727,radius11,radius11_checked,chord_keep%(1786,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (1728,radius12,radius12_checked,chord_keep%(1787,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(5,0),(1,5)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (1729,radius13,radius13_checked,chord_keep%(1788,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (1730,radius14,radius14_checked,chord_keep%(1789,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(1,0),(32,5)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (1731,radius15,radius15_checked,chord_keep%(1790,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(1,0),(4,5)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (1732,radius16,radius16_checked,chord_keep%(1791,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 3, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (1733,radius17,radius17_checked,chord_keep%(1792,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 3, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (1734,radius18,radius18_checked,chord_keep%(1793,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 3, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(4,6)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (1735,radius19,radius19_checked,chord_keep%(1794,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 3, .single 6, .copy 13]),chord_close%(⟨[0,6],[(10,0),(1,6)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (1736,radius20,radius20_checked,chord_keep%(1795,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(1,0),(8,5)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (1737,radius21,radius21_checked,chord_keep%(1796,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (1738,radius27,radius27_checked,chord_keep%(1797,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 2, .single 1, .single 4, .copy 11]),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (1739,radius28,radius28_checked,chord_keep%(1798,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 2, .single 1, .single 4, .copy 11]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (1740,radius29,radius29_checked,chord_keep%(1799,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 2, .single 1, .single 4, .copy 11]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (1741,radius30,radius30_checked,chord_keep%(1800,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 2, .single 1, .single 4, .copy 11]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (1742,radius31,radius31_checked,chord_keep%(1801,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(5,6)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (1743,radius32,radius32_checked,chord_keep%(1802,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (1744,radius33,radius33_checked,chord_keep%(1803,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(2,0),(1,6)]⟩))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (1745,radius34,radius34_checked,chord_keep%(1804,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(2,0),(5,6)]⟩))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (1746,radius35,radius35_checked,chord_keep%(1805,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(8,6)]⟩))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (1747,radius36,radius36_checked,chord_keep%(1806,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(16,6)]⟩))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (1748,radius37,radius37_checked,chord_keep%(1807,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (1749,radius38,radius38_checked,chord_keep%(1808,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(125,0),(4,6)]⟩))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (1750,radius39,radius39_checked,chord_keep%(1809,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (1751,radius40,radius40_checked,chord_keep%(1810,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (1752,radius41,radius41_checked,chord_keep%(1811,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (1753,radius42,radius42_checked,chord_keep%(1812,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(2,0),(1,6)]⟩))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (1754,radius43,radius43_checked,chord_keep%(1813,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,7],[(1,0),(10,7)]⟩))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (1755,radius44,radius44_checked,chord_keep%(1814,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,7],[(1,0),(25,7)]⟩))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (1756,radius45,radius45_checked,chord_keep%(1815,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (1757,radius46,radius46_checked,chord_keep%(1816,[.single 1, .single 2, .single 3, .single 4, .single 5, .pair 2 6, .single 0, .pair 1 8, .single 9, .single 9, .single 5, .single 2, .single 0, .copy 14]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (1758,radius47,radius47_checked,chord_keep%(1817,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .pair 2 6, .single 0, .pair 0 1, .pair 0 1, .single 5, .single 2, .single 0, .copy 14]),chord_close%(⟨[0,7],[(4,0),(5,7)]⟩))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (1759,radius48,radius48_checked,chord_keep%(1818,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 1, .single 6, .copy 13]),chord_close%(⟨[0,6],[(5,0),(1,6)]⟩))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (1760,radius49,radius49_checked,chord_keep%(1819,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 1, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (1761,radius50,radius50_checked,chord_keep%(1820,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (1762,radius51,radius51_checked,chord_keep%(1821,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (1763,radius52,radius52_checked,chord_keep%(1822,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (1764,radius53,radius53_checked,chord_keep%(1823,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (1765,radius54,radius54_checked,chord_keep%(1824,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(5,6)]⟩))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (1766,radius55,radius55_checked,chord_keep%(1825,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(40,0),(1,6)]⟩))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (1767,radius56,radius56_checked,chord_keep%(1826,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(20,0),(1,6)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (1768,radius57,radius57_checked,chord_keep%(1827,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (1769,radius58,radius58_checked,chord_keep%(1828,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 7, .single 8, .single 8, .pair 0 3, .single 1, .single 0, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (1770,radius59,radius59_checked,chord_keep%(1829,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 8, .single 9, .single 9, .pair 0 3, .single 1, .single 0, .copy 14]),chord_close%(⟨[0,7],[(4,0),(1,7)]⟩))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (1771,radius60,radius60_checked,chord_keep%(1830,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 8, .single 9, .single 9, .pair 0 3, .single 1, .single 0, .copy 14]),chord_close%(⟨[0,7],[(5,0),(4,7)]⟩))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (1772,radius61,radius61_checked,chord_keep%(1831,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 8, .single 9, .single 9, .pair 0 3, .single 1, .single 0, .copy 14]),chord_close%(⟨[0,7],[(1,0),(1000,7)]⟩))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (1773,radius62,radius62_checked,chord_keep%(1832,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 8, .single 9, .single 9, .pair 0 3, .single 1, .single 0, .copy 14]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (1774,radius63,radius63_checked,chord_keep%(1833,[.single 1, .single 2, .pair 1 3, .pair 0 3, .single 0, .pair 1 8, .single 9, .single 9, .pair 0 3, .single 1, .single 0, .copy 14]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53, plan54, plan55, plan56, plan57, plan58]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout701Domain9_0Ids := by rfl
def outputIds : List (Fin poseCount) := [1775,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791,1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout701Domain9_15Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout701Domain9_15Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout701Domain9_0 (q 0))
    (h0 : OrientedPoseCovered continuousScout701Domain1_3 (q 1))
    (h1 : OrientedPoseCovered continuousScout701Domain6_13 (q 2))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (q 3))
    : OrientedPoseCovered continuousScout701Domain9_15 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout701Domain9_0Ids continuousScout701Domain9_15Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain1_3Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain6_13Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain10_6Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![8192,2,256,16384]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout701Domain9_0 (p.square (ownerIndex p 8192)))
    (h0 : OrientedPoseCovered continuousScout701Domain1_3 (p.square (ownerIndex p 2)))
    (h1 : OrientedPoseCovered continuousScout701Domain6_13 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)))
    : OrientedPoseCovered continuousScout701Domain9_15 (p.square (ownerIndex p 8192)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout701Domain9_0 continuousScout701Domain9_15
    ![continuousScout701Domain1_3,continuousScout701Domain6_13,continuousScout701Domain10_6]
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
end N12Compact.Preservation.Chords.C701Step14

import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C701

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C701Step20
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C701

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (83168997/100000000)
def hi : ℚ := (93512191/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (168,radius0,radius0_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (169,radius1,radius1_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (170,radius2,radius2_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (171,radius3,radius3_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (172,radius4,radius4_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (173,radius5,radius5_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (174,radius6,radius6_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (175,radius7,radius7_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (176,radius8,radius8_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (177,radius9,radius9_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (178,radius10,radius10_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (179,radius11,radius11_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (180,radius12,radius12_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (181,radius13,radius13_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (182,radius14,radius14_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (183,radius44,radius44_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (184,radius45,radius45_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (185,radius46,radius46_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (186,radius47,radius47_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (187,radius48,radius48_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (188,radius49,radius49_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (189,radius50,radius50_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (190,radius51,radius51_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (191,radius52,radius52_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (192,radius53,radius53_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (193,radius54,radius54_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (194,radius55,radius55_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (195,radius56,radius56_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (196,radius57,radius57_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (197,radius58,radius58_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (198,radius59,radius59_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (199,radius60,radius60_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (200,radius61,radius61_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (201,radius62,radius62_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (202,radius63,radius63_checked,[.single 0, .single 4])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout701Domain0_20Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (854,radius0,radius0_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (855,radius1,radius1_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (856,radius2,radius2_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (857,radius3,radius3_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (858,radius4,radius4_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (859,radius5,radius5_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (860,radius6,radius6_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (861,radius7,radius7_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (862,radius8,radius8_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (863,radius48,radius48_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (864,radius49,radius49_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (865,radius50,radius50_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (866,radius51,radius51_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (867,radius52,radius52_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (868,radius53,radius53_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (869,radius54,radius54_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (870,radius55,radius55_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (871,radius56,radius56_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (872,radius57,radius57_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (873,radius58,radius58_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (874,radius59,radius59_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (875,radius60,radius60_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (876,radius61,radius61_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (877,radius62,radius62_checked,[.single 0, .single 2])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (878,radius63,radius63_checked,[.single 0, .single 2])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout701Domain2_5Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (1887,radius0,radius0_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (1888,radius1,radius1_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (1889,radius2,radius2_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (1890,radius3,radius3_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (1891,radius4,radius4_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (1892,radius5,radius5_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (1893,radius6,radius6_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (1894,radius7,radius7_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (1895,radius8,radius8_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (1896,radius9,radius9_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (1897,radius10,radius10_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (1898,radius11,radius11_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (1899,radius12,radius12_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (1900,radius13,radius13_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (1901,radius14,radius14_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (1902,radius15,radius15_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (1903,radius16,radius16_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (1904,radius17,radius17_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (1905,radius18,radius18_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (1906,radius31,radius31_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (1907,radius32,radius32_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (1908,radius33,radius33_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (1909,radius34,radius34_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (1910,radius35,radius35_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (1911,radius36,radius36_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (1912,radius37,radius37_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (1913,radius38,radius38_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (1914,radius39,radius39_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (1915,radius40,radius40_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (1916,radius41,radius41_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (1917,radius42,radius42_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (1918,radius43,radius43_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (1919,radius44,radius44_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (1920,radius45,radius45_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (1921,radius46,radius46_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (1922,radius47,radius47_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (1923,radius48,radius48_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (1924,radius49,radius49_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (1925,radius50,radius50_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (1926,radius51,radius51_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (1927,radius52,radius52_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (1928,radius53,radius53_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (1929,radius54,radius54_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (1930,radius55,radius55_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (1931,radius56,radius56_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (1932,radius57,radius57_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (1933,radius58,radius58_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (1934,radius59,radius59_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (1935,radius60,radius60_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (1936,radius61,radius61_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (1937,radius62,radius62_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (1938,radius63,radius63_checked,[.single 0, .single 4])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout701Domain9_17Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (695,radius0,radius0_checked,chord_close%(⟨[0,1],[(1,0),(2,1)]⟩),chord_keep%(641,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (696,radius1,radius1_checked,chord_close%(⟨[0,1],[(2,0),(1,1)]⟩),chord_keep%(642,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 1, .single 6, .copy 13]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (697,radius2,radius2_checked,chord_close%(⟨[0,1],[(1,0),(2,1)]⟩),chord_keep%(643,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 1, .single 6, .copy 13]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (698,radius3,radius3_checked,chord_close%(⟨[0,1],[(1,0),(1,1)]⟩),chord_keep%(644,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 1, .single 6, .copy 13]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (699,radius4,radius4_checked,chord_close%(⟨[0,1],[(1,0),(8,1)]⟩),chord_keep%(645,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 1, .single 6, .copy 13]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (700,radius5,radius5_checked,chord_close%(⟨[0,1],[(5,0),(1,1)]⟩),chord_keep%(646,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (701,radius6,radius6_checked,chord_close%(⟨[0,1],[(16,0),(1,1)]⟩),chord_keep%(647,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 1, .single 5, .copy 13]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (702,radius7,radius7_checked,chord_close%(⟨[0,1],[(5,0),(1,1)]⟩),chord_keep%(648,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 1, .single 5, .copy 13]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (703,radius8,radius8_checked,chord_close%(⟨[0,1],[(1,0),(5,1)]⟩),chord_keep%(649,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 1, .single 5, .copy 13]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (704,radius9,radius9_checked,chord_close%(⟨[0,1],[(2,0),(1,1)]⟩),chord_keep%(650,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 1, .single 5, .copy 13]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (705,radius10,radius10_checked,chord_close%(⟨[0,1],[(1,0),(2,1)]⟩),chord_keep%(651,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 3, .single 1, .single 5, .copy 13]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (706,radius11,radius11_checked,chord_close%(⟨[0,1],[(1,0),(1,1)]⟩),chord_keep%(652,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 4, .copy 12]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (707,radius12,radius12_checked,chord_close%(⟨[0,1],[(1,0),(20,1)]⟩),chord_keep%(653,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 4, .copy 12]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (708,radius13,radius13_checked,chord_close%(⟨[0,1],[(1,0),(5,1)]⟩),chord_keep%(654,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 4, .copy 11]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (709,radius33,radius33_checked,chord_close%(⟨[0,1],[(1,0),(4,1)]⟩),chord_keep%(655,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (710,radius34,radius34_checked,chord_close%(⟨[0,1],[(10,0),(1,1)]⟩),chord_keep%(656,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (711,radius35,radius35_checked,chord_close%(⟨[0,1],[(4,0),(1,1)]⟩),chord_keep%(657,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (712,radius36,radius36_checked,chord_close%(⟨[0,1],[(1,0),(8,1)]⟩),chord_keep%(658,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (713,radius37,radius37_checked,chord_close%(⟨[0,1],[(1,0),(50,1)]⟩),chord_keep%(659,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (714,radius38,radius38_checked,chord_close%(⟨[0,1],[(1,0),(32,1)]⟩),chord_keep%(660,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (715,radius39,radius39_checked,chord_close%(⟨[0,1],[(5,0),(1,1)]⟩),chord_keep%(661,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (716,radius40,radius40_checked,chord_close%(⟨[0,1],[(1,0),(2,1)]⟩),chord_keep%(662,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (717,radius41,radius41_checked,chord_close%(⟨[0,1],[(5,0),(2,1)]⟩),chord_keep%(663,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (718,radius42,radius42_checked,chord_close%(⟨[0,1],[(5,0),(1,1)]⟩),chord_keep%(664,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (719,radius43,radius43_checked,chord_close%(⟨[0,1],[(1,0),(1,1)]⟩),chord_keep%(665,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (720,radius44,radius44_checked,chord_close%(⟨[0,1],[(1,0),(16,1)]⟩),chord_keep%(666,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (721,radius45,radius45_checked,chord_close%(⟨[0,1],[(5,0),(4,1)]⟩),chord_keep%(667,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (722,radius46,radius46_checked,chord_close%(⟨[0,1],[(5,0),(1,1)]⟩),chord_keep%(668,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (723,radius47,radius47_checked,chord_close%(⟨[0,1],[(1,0),(4,1)]⟩),chord_keep%(669,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (724,radius48,radius48_checked,chord_close%(⟨[0,1],[(1,0),(32,1)]⟩),chord_keep%(670,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 6, .single 3, .single 1, .single 5, .copy 11]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (725,radius49,radius49_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(671,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (726,radius50,radius50_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_keep%(672,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (727,radius51,radius51_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_keep%(673,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (728,radius52,radius52_checked,chord_close%(⟨[0,2],[(10,0),(1,2)]⟩),chord_keep%(674,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (729,radius53,radius53_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(675,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (730,radius54,radius54_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(676,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (731,radius55,radius55_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(677,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (732,radius56,radius56_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(678,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (733,radius57,radius57_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_keep%(679,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (734,radius58,radius58_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(680,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 0, .single 7, .copy 13]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (735,radius59,radius59_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(681,[.single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 6, .single 0, .single 8, .copy 14]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (736,radius60,radius60_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(682,[.single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 6, .single 0, .single 8, .copy 14]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (737,radius61,radius61_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(683,[.single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 6, .single 0, .single 8, .copy 14]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (738,radius62,radius62_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(684,[.single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 0, .single 7, .copy 13]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (739,radius63,radius63_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(685,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 0, .single 7, .copy 13]))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout701Domain1_3Ids := by rfl
def outputIds : List (Fin poseCount) := [641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout701Domain1_21Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout701Domain1_21Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout701Domain1_3 (q 0))
    (h0 : OrientedPoseCovered continuousScout701Domain0_20 (q 1))
    (h1 : OrientedPoseCovered continuousScout701Domain2_5 (q 2))
    (h2 : OrientedPoseCovered continuousScout701Domain9_17 (q 3))
    : OrientedPoseCovered continuousScout701Domain1_21 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout701Domain1_3Ids continuousScout701Domain1_21Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain0_20Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain2_5Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout701Domain9_17Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![2,1,12,8192]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout701Domain1_3 (p.square (ownerIndex p 2)))
    (h0 : OrientedPoseCovered continuousScout701Domain0_20 (p.square (ownerIndex p 1)))
    (h1 : OrientedPoseCovered continuousScout701Domain2_5 (p.square (ownerIndex p 12)))
    (h2 : OrientedPoseCovered continuousScout701Domain9_17 (p.square (ownerIndex p 8192)))
    : OrientedPoseCovered continuousScout701Domain1_21 (p.square (ownerIndex p 2)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout701Domain1_3 continuousScout701Domain1_21
    ![continuousScout701Domain0_20,continuousScout701Domain2_5,continuousScout701Domain9_17]
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
end N12Compact.Preservation.Chords.C701Step20

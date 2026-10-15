import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C978

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C978Step13
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C978

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (48490847/20000000)
def hi : ℚ := (31733877/12500000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (8591,radius0,radius0_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (8592,radius1,radius1_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (8593,radius2,radius2_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (8594,radius3,radius3_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (8595,radius4,radius4_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (8596,radius5,radius5_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (8597,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (8598,radius7,radius7_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (8599,radius8,radius8_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (8600,radius9,radius9_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (8601,radius62,radius62_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (8602,radius63,radius63_checked,[.single 1, .single 6])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout978Domain7_3Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (8603,radius0,radius0_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (8604,radius1,radius1_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (8605,radius2,radius2_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (8606,radius3,radius3_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (8607,radius4,radius4_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (8608,radius5,radius5_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (8609,radius6,radius6_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (8610,radius7,radius7_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (8611,radius8,radius8_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (8612,radius9,radius9_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (8613,radius61,radius61_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (8614,radius62,radius62_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (8615,radius63,radius63_checked,[.single 1, .single 5])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout978Domain8_4Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (7929,radius0,radius0_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (7930,radius1,radius1_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (7931,radius2,radius2_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (7932,radius3,radius3_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (7933,radius4,radius4_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (7934,radius5,radius5_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (7935,radius6,radius6_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (7936,radius7,radius7_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (7937,radius8,radius8_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (7938,radius9,radius9_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (7939,radius10,radius10_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (7940,radius11,radius11_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (7941,radius12,radius12_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (7942,radius13,radius13_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (7943,radius14,radius14_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (7944,radius15,radius15_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (7945,radius16,radius16_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (7946,radius17,radius17_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (7947,radius18,radius18_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (7948,radius19,radius19_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (7949,radius20,radius20_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (7950,radius21,radius21_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (7951,radius22,radius22_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (7952,radius23,radius23_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (7953,radius24,radius24_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (7954,radius25,radius25_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (7955,radius26,radius26_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (7956,radius27,radius27_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (7957,radius28,radius28_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (7958,radius29,radius29_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (7959,radius30,radius30_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (7960,radius31,radius31_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (7961,radius32,radius32_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (7962,radius33,radius33_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (7963,radius34,radius34_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (7964,radius35,radius35_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (7965,radius36,radius36_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (7966,radius37,radius37_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (7967,radius38,radius38_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (7968,radius39,radius39_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (7969,radius40,radius40_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (7970,radius45,radius45_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (7971,radius46,radius46_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (7972,radius47,radius47_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (7973,radius48,radius48_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (7974,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (7975,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (7976,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (7977,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (7978,radius53,radius53_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (7979,radius54,radius54_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (7980,radius55,radius55_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_52 (dictionary,horizontal,lo,hi) := (7981,radius56,radius56_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_53 (dictionary,horizontal,lo,hi) := (7982,radius57,radius57_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_54 (dictionary,horizontal,lo,hi) := (7983,radius58,radius58_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_55 (dictionary,horizontal,lo,hi) := (7984,radius59,radius59_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_56 (dictionary,horizontal,lo,hi) := (7985,radius60,radius60_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_57 (dictionary,horizontal,lo,hi) := (7986,radius61,radius61_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_58 (dictionary,horizontal,lo,hi) := (7987,radius62,radius62_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_59 (dictionary,horizontal,lo,hi) := (7988,radius63,radius63_checked,[.single 1, .single 5])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51, neighbor2_52, neighbor2_53, neighbor2_54, neighbor2_55, neighbor2_56, neighbor2_57, neighbor2_58, neighbor2_59]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout978Domain10_13Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (7989,radius0,radius0_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (7990,radius1,radius1_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(4000,7)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (7991,radius2,radius2_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (7992,radius3,radius3_checked,chord_close%(⟨[0,2],[(4,0),(125,2)]⟩),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (7993,radius4,radius4_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (7994,radius5,radius5_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,8],[(2,0),(1,8)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (7995,radius6,radius6_checked,chord_close%(⟨[0,2],[(10,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (7996,radius7,radius7_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(8053,[.single 0, .pair 0 6, .pair 6 7, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 6, .single 0, .single 7, .copy 14]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (7997,radius8,radius8_checked,chord_close%(⟨[0,2],[(5,0),(4,2)]⟩),chord_keep%(8054,[.single 0, .pair 0 6, .pair 6 7, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 6, .single 0, .single 7, .copy 15]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (7998,radius9,radius9_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(8055,[.single 0, .pair 0 6, .pair 6 7, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 6, .single 0, .single 7, .copy 15]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (7999,radius10,radius10_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8056,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 7, .copy 15]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (8000,radius11,radius11_checked,chord_close%(⟨[0,2],[(1,0),(16,2)]⟩),chord_keep%(8057,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 7, .copy 15]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (8001,radius12,radius12_checked,chord_close%(⟨[0,2],[(5,0),(4,2)]⟩),chord_keep%(8058,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 6, .copy 14]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (8002,radius13,radius13_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8059,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 6, .copy 14]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (8003,radius14,radius14_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(8060,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 6, .copy 14]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (8004,radius15,radius15_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8061,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 6, .copy 14]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (8005,radius16,radius16_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(8062,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 6, .copy 14]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (8006,radius17,radius17_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8063,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 6, .copy 14]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (8007,radius18,radius18_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(8064,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 6, .copy 14]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (8008,radius19,radius19_checked,chord_close%(⟨[0,2],[(100,0),(1,2)]⟩),chord_keep%(8065,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 6, .copy 14]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (8009,radius20,radius20_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8066,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 6, .copy 14]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (8010,radius21,radius21_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(8067,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 6, .copy 14]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (8011,radius22,radius22_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_keep%(8068,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (8012,radius23,radius23_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(8069,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (8013,radius24,radius24_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(8070,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (8014,radius25,radius25_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(8071,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (8015,radius26,radius26_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(8072,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (8016,radius27,radius27_checked,chord_close%(⟨[0,2],[(16,0),(25,2)]⟩),chord_keep%(8073,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (8017,radius28,radius28_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8074,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (8018,radius29,radius29_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(8075,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (8019,radius30,radius30_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_keep%(8076,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .pair 4 7, .pair 0 7, .pair 0 7, .single 4, .single 0, .single 6, .copy 13]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (8020,radius31,radius31_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8077,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 7, .copy 14]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (8021,radius32,radius32_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(8078,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 7, .copy 14]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (8022,radius33,radius33_checked,chord_close%(⟨[0,2],[(4,0),(1,2)]⟩),chord_keep%(8079,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 7, .copy 14]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (8023,radius34,radius34_checked,chord_close%(⟨[0,2],[(8,0),(1,2)]⟩),chord_keep%(8080,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .pair 4 9, .pair 0 9, .pair 0 9, .single 4, .single 0, .single 8, .copy 15]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (8024,radius35,radius35_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8081,[.single 0, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .single 4, .single 0, .single 7, .copy 14]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (8025,radius36,radius36_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(8082,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 7, .copy 14]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (8026,radius37,radius37_checked,chord_close%(⟨[0,2],[(20,0),(1,2)]⟩),chord_keep%(8083,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 7, .copy 14]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (8027,radius38,radius38_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(8084,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 7, .copy 14]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (8028,radius39,radius39_checked,chord_close%(⟨[0,2],[(1,0),(200,2)]⟩),chord_keep%(8085,[.single 0, .pair 0 5, .pair 5 6, .single 6, .single 7, .pair 4 8, .pair 0 8, .pair 0 8, .pair 0 5, .single 0, .single 7, .copy 14]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (8029,radius40,radius40_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(8086,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 8, .copy 15]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (8030,radius41,radius41_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_keep%(8087,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 8, .copy 15]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (8031,radius42,radius42_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(8088,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 8, .copy 15]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (8032,radius43,radius43_checked,chord_close%(⟨[0,3],[(1,0),(2,3)]⟩),chord_keep%(8089,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 8, .copy 15]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (8033,radius44,radius44_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(8090,[.single 0, .pair 0 6, .pair 6 7, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 6, .single 0, .single 8, .copy 15]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (8034,radius45,radius45_checked,chord_close%(⟨[0,3],[(1,0),(2,3)]⟩),chord_keep%(8091,[.single 0, .pair 5 6, .single 6, .single 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .single 6, .single 0, .single 8, .copy 15]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (8035,radius46,radius46_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(8092,[.single 0, .pair 0 7, .pair 1 7, .single 8, .pair 5 9, .pair 0 9, .pair 0 9, .pair 0 7, .single 0, .single 8, .copy 15]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (8036,radius47,radius47_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(8093,[.single 0, .pair 0 8, .pair 1 8, .single 9, .pair 5 10, .pair 0 10, .pair 0 10, .pair 0 8, .single 0, .single 9, .copy 16]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (8037,radius48,radius48_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_keep%(8094,[.single 0, .pair 0 8, .pair 1 8, .single 9, .pair 5 10, .pair 0 10, .pair 0 10, .pair 0 8, .single 0, .single 9, .copy 16]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (8038,radius49,radius49_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(8095,[.single 0, .pair 0 8, .pair 1 8, .single 9, .pair 8 10, .pair 0 10, .pair 0 10, .pair 0 8, .single 0, .single 9, .copy 16]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (8039,radius50,radius50_checked,chord_close%(⟨[0,3],[(4,0),(1,3)]⟩),chord_close%(⟨[0,9],[(1,0),(1,9)]⟩))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (8040,radius51,radius51_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_close%(⟨[0,9],[(1,0),(4,9)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (8041,radius52,radius52_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,8],[(1,0),(2,8)]⟩))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (8042,radius53,radius53_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,8],[(10,0),(1,8)]⟩))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (8043,radius54,radius54_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (8044,radius55,radius55_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (8045,radius56,radius56_checked,chord_close%(⟨[0,2],[(2,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(4,7)]⟩))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (8046,radius57,radius57_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (8047,radius58,radius58_checked,chord_close%(⟨[0,2],[(1,0),(16,2)]⟩),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (8048,radius59,radius59_checked,chord_close%(⟨[0,2],[(1,0),(25,2)]⟩),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (8049,radius60,radius60_checked,chord_close%(⟨[0,2],[(20,0),(1,2)]⟩),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (8050,radius61,radius61_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (8051,radius62,radius62_checked,chord_close%(⟨[0,2],[(1,0),(16,2)]⟩),chord_close%(⟨[0,7],[(4,0),(1,7)]⟩))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (8052,radius63,radius63_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53, plan54, plan55, plan56, plan57, plan58, plan59,
    plan60, plan61, plan62, plan63]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout978Domain11_0Ids := by rfl
def outputIds : List (Fin poseCount) := [8053,8054,8055,8056,8057,8058,8059,8060,8061,8062,8063,8064,8065,8066,8067,8068,8069,8070,8071,8072,8073,8074,8075,8076,8077,8078,8079,8080,8081,8082,8083,8084,8085,8086,8087,8088,8089,8090,8091,8092,8093,8094,8095]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout978Domain11_14Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout978Domain11_14Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout978Domain11_0 (q 0))
    (h0 : OrientedPoseCovered continuousScout978Domain7_3 (q 1))
    (h1 : OrientedPoseCovered continuousScout978Domain8_4 (q 2))
    (h2 : OrientedPoseCovered continuousScout978Domain10_13 (q 3))
    : OrientedPoseCovered continuousScout978Domain11_14 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout978Domain11_0Ids continuousScout978Domain11_14Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout978Domain7_3Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout978Domain8_4Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout978Domain10_13Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![33792,2048,4096,16384]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout978Domain11_0 (p.square (ownerIndex p 33792)))
    (h0 : OrientedPoseCovered continuousScout978Domain7_3 (p.square (ownerIndex p 2048)))
    (h1 : OrientedPoseCovered continuousScout978Domain8_4 (p.square (ownerIndex p 4096)))
    (h2 : OrientedPoseCovered continuousScout978Domain10_13 (p.square (ownerIndex p 16384)))
    : OrientedPoseCovered continuousScout978Domain11_14 (p.square (ownerIndex p 33792)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout978Domain11_0 continuousScout978Domain11_14
    ![continuousScout978Domain7_3,continuousScout978Domain8_4,continuousScout978Domain10_13]
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
end N12Compact.Preservation.Chords.C978Step13

import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C973

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C973Step15
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C973

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (9644853/3125000)
def hi : ℚ := (63250151/20000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (6558,radius0,radius0_checked,[.single 3, .single 5])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (6559,radius1,radius1_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (6560,radius2,radius2_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (6561,radius3,radius3_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (6562,radius4,radius4_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (6563,radius5,radius5_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (6564,radius6,radius6_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (6565,radius7,radius7_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (6566,radius8,radius8_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (6567,radius9,radius9_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (6568,radius10,radius10_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (6569,radius11,radius11_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (6570,radius12,radius12_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (6571,radius13,radius13_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (6572,radius14,radius14_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (6573,radius15,radius15_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (6574,radius16,radius16_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (6575,radius17,radius17_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (6576,radius18,radius18_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (6577,radius19,radius19_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (6578,radius20,radius20_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (6579,radius21,radius21_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (6580,radius22,radius22_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (6581,radius23,radius23_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (6582,radius24,radius24_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (6583,radius25,radius25_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (6584,radius26,radius26_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (6585,radius27,radius27_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (6586,radius28,radius28_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (6587,radius29,radius29_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (6588,radius30,radius30_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (6589,radius31,radius31_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (6590,radius32,radius32_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (6591,radius33,radius33_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (6592,radius34,radius34_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (6593,radius35,radius35_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (6594,radius36,radius36_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (6595,radius37,radius37_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (6596,radius38,radius38_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (6597,radius39,radius39_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (6598,radius40,radius40_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (6599,radius41,radius41_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (6600,radius42,radius42_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (6601,radius43,radius43_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (6602,radius44,radius44_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_45 (dictionary,horizontal,lo,hi) := (6603,radius45,radius45_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_46 (dictionary,horizontal,lo,hi) := (6604,radius46,radius46_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_47 (dictionary,horizontal,lo,hi) := (6605,radius47,radius47_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_48 (dictionary,horizontal,lo,hi) := (6606,radius48,radius48_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_49 (dictionary,horizontal,lo,hi) := (6607,radius49,radius49_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_50 (dictionary,horizontal,lo,hi) := (6608,radius50,radius50_checked,[.single 1, .single 3])
checked_chord_neighbor neighbor0_51 (dictionary,horizontal,lo,hi) := (6609,radius51,radius51_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_52 (dictionary,horizontal,lo,hi) := (6610,radius52,radius52_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_53 (dictionary,horizontal,lo,hi) := (6611,radius53,radius53_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_54 (dictionary,horizontal,lo,hi) := (6612,radius54,radius54_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_55 (dictionary,horizontal,lo,hi) := (6613,radius55,radius55_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_56 (dictionary,horizontal,lo,hi) := (6614,radius56,radius56_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_57 (dictionary,horizontal,lo,hi) := (6615,radius57,radius57_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_58 (dictionary,horizontal,lo,hi) := (6616,radius58,radius58_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_59 (dictionary,horizontal,lo,hi) := (6617,radius59,radius59_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_60 (dictionary,horizontal,lo,hi) := (6618,radius60,radius60_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_61 (dictionary,horizontal,lo,hi) := (6619,radius61,radius61_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_62 (dictionary,horizontal,lo,hi) := (6620,radius62,radius62_checked,[.single 2, .single 4])
checked_chord_neighbor neighbor0_63 (dictionary,horizontal,lo,hi) := (6621,radius63,radius63_checked,[.single 2, .single 4])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44, neighbor0_45, neighbor0_46, neighbor0_47,
    neighbor0_48, neighbor0_49, neighbor0_50, neighbor0_51, neighbor0_52, neighbor0_53, neighbor0_54, neighbor0_55, neighbor0_56, neighbor0_57, neighbor0_58, neighbor0_59,
    neighbor0_60, neighbor0_61, neighbor0_62, neighbor0_63]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout973Domain3_13Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (6622,radius0,radius0_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (6623,radius1,radius1_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (6624,radius2,radius2_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (6625,radius3,radius3_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (6626,radius4,radius4_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (6627,radius5,radius5_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (6628,radius6,radius6_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (6629,radius7,radius7_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (6630,radius8,radius8_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (6631,radius9,radius9_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (6632,radius10,radius10_checked,[.single 0, .single 3])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (6633,radius14,radius14_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (6634,radius15,radius15_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (6635,radius16,radius16_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (6636,radius17,radius17_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (6637,radius18,radius18_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (6638,radius19,radius19_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (6639,radius20,radius20_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (6640,radius21,radius21_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (6641,radius22,radius22_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (6642,radius23,radius23_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (6643,radius24,radius24_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (6644,radius25,radius25_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (6645,radius26,radius26_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (6646,radius27,radius27_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (6647,radius28,radius28_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (6648,radius29,radius29_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (6649,radius30,radius30_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (6650,radius31,radius31_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (6651,radius32,radius32_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (6652,radius33,radius33_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (6653,radius34,radius34_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (6654,radius35,radius35_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (6655,radius36,radius36_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (6656,radius37,radius37_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (6657,radius38,radius38_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (6658,radius39,radius39_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (6659,radius40,radius40_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (6660,radius41,radius41_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (6661,radius42,radius42_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (6662,radius43,radius43_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (6663,radius44,radius44_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (6664,radius45,radius45_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (6665,radius46,radius46_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (6666,radius47,radius47_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (6667,radius48,radius48_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (6668,radius49,radius49_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (6669,radius50,radius50_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (6670,radius51,radius51_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (6671,radius52,radius52_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (6672,radius53,radius53_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (6673,radius54,radius54_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (6674,radius55,radius55_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (6675,radius56,radius56_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (6676,radius57,radius57_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (6677,radius58,radius58_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (6678,radius59,radius59_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (6679,radius60,radius60_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (6680,radius61,radius61_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (6681,radius62,radius62_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (6682,radius63,radius63_checked,[.single 1, .single 5])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53, neighbor1_54, neighbor1_55, neighbor1_56, neighbor1_57, neighbor1_58, neighbor1_59,
    neighbor1_60]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout973Domain4_14Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (6250,radius0,radius0_checked,[.single 2, .single 7])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (6251,radius1,radius1_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (6252,radius2,radius2_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (6253,radius3,radius3_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (6254,radius4,radius4_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (6255,radius5,radius5_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (6256,radius6,radius6_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (6257,radius7,radius7_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (6258,radius8,radius8_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (6259,radius9,radius9_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (6260,radius10,radius10_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (6261,radius11,radius11_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (6262,radius12,radius12_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (6263,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (6264,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (6265,radius15,radius15_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (6266,radius16,radius16_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (6267,radius17,radius17_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (6268,radius18,radius18_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (6269,radius19,radius19_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (6270,radius20,radius20_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (6271,radius21,radius21_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (6272,radius22,radius22_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (6273,radius23,radius23_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (6274,radius24,radius24_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (6275,radius25,radius25_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (6276,radius26,radius26_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (6277,radius27,radius27_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (6278,radius28,radius28_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (6279,radius29,radius29_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (6280,radius30,radius30_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (6281,radius31,radius31_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (6282,radius32,radius32_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (6283,radius33,radius33_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (6284,radius34,radius34_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (6285,radius35,radius35_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (6286,radius36,radius36_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (6287,radius37,radius37_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (6288,radius38,radius38_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (6289,radius39,radius39_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (6290,radius40,radius40_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (6291,radius41,radius41_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (6292,radius42,radius42_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (6293,radius43,radius43_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (6294,radius44,radius44_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (6295,radius45,radius45_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (6296,radius46,radius46_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (6297,radius47,radius47_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (6298,radius48,radius48_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (6299,radius49,radius49_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (6300,radius50,radius50_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (6301,radius51,radius51_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_52 (dictionary,horizontal,lo,hi) := (6302,radius52,radius52_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_53 (dictionary,horizontal,lo,hi) := (6303,radius53,radius53_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_54 (dictionary,horizontal,lo,hi) := (6304,radius54,radius54_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_55 (dictionary,horizontal,lo,hi) := (6305,radius55,radius55_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_56 (dictionary,horizontal,lo,hi) := (6306,radius56,radius56_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_57 (dictionary,horizontal,lo,hi) := (6307,radius57,radius57_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_58 (dictionary,horizontal,lo,hi) := (6308,radius58,radius58_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_59 (dictionary,horizontal,lo,hi) := (6309,radius59,radius59_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_60 (dictionary,horizontal,lo,hi) := (6310,radius60,radius60_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_61 (dictionary,horizontal,lo,hi) := (6311,radius61,radius61_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_62 (dictionary,horizontal,lo,hi) := (6312,radius62,radius62_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_63 (dictionary,horizontal,lo,hi) := (6313,radius63,radius63_checked,[.single 2, .single 5])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51, neighbor2_52, neighbor2_53, neighbor2_54, neighbor2_55, neighbor2_56, neighbor2_57, neighbor2_58, neighbor2_59,
    neighbor2_60, neighbor2_61, neighbor2_62, neighbor2_63]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout973Domain11_0Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (7478,radius0,radius0_checked,chord_keep%(7532,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 2 7, .single 0, .pair 1 11, .single 12, .single 12, .single 4, .single 2, .single 0, .copy 17]),chord_close%(⟨[0,9],[(1,0),(5,9)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (7479,radius1,radius1_checked,chord_keep%(7533,[.single 1, .single 2, .single 3, .single 4, .single 5, .pair 2 6, .single 0, .pair 1 10, .single 11, .single 11, .single 4, .single 2, .single 0, .copy 16]),chord_close%(⟨[0,8],[(2,0),(1,8)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (7480,radius2,radius2_checked,chord_keep%(7534,[.pair 1 2, .single 2, .single 3, .single 4, .pair 2 5, .single 0, .pair 0 1, .pair 0 1, .single 4, .single 2, .single 0, .copy 15]),chord_close%(⟨[0,7],[(5,0),(2,7)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (7481,radius3,radius3_checked,chord_keep%(7535,[.pair 1 2, .single 2, .single 3, .single 4, .pair 2 5, .single 0, .pair 0 1, .pair 0 1, .single 4, .single 2, .single 0, .copy 15]),chord_close%(⟨[0,7],[(1,0),(5,7)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (7482,radius4,radius4_checked,chord_keep%(7536,[.pair 1 2, .single 2, .single 3, .single 4, .pair 2 5, .single 0, .pair 0 1, .pair 0 1, .single 4, .single 2, .single 0, .copy 15]),chord_close%(⟨[0,7],[(4,0),(1,7)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (7483,radius5,radius5_checked,chord_keep%(7537,[.pair 1 2, .single 2, .single 3, .single 4, .pair 2 5, .single 0, .pair 0 1, .pair 0 1, .single 4, .single 2, .single 0, .copy 15]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (7484,radius6,radius6_checked,chord_keep%(7538,[.single 1, .single 2, .single 3, .single 4, .pair 2 5, .single 0, .pair 1 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 0, .copy 14]),chord_close%(⟨[0,6],[(20,0),(1,6)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (7485,radius7,radius7_checked,chord_keep%(7539,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 6, .copy 14]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (7486,radius8,radius8_checked,chord_keep%(7540,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,7],[(5,0),(8,7)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (7487,radius9,radius9_checked,chord_keep%(7541,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (7488,radius10,radius10_checked,chord_keep%(7542,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (7489,radius11,radius11_checked,chord_keep%(7543,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (7490,radius12,radius12_checked,chord_keep%(7544,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (7491,radius13,radius13_checked,chord_keep%(7545,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (7492,radius14,radius14_checked,chord_keep%(7546,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(2,0),(1,6)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (7493,radius15,radius15_checked,chord_keep%(7547,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(5,7)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (7494,radius16,radius16_checked,chord_keep%(7548,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 8, .copy 14]),chord_close%(⟨[0,8],[(1,0),(5,8)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (7495,radius17,radius17_checked,chord_keep%(7549,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (7496,radius18,radius18_checked,chord_keep%(7550,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (7497,radius19,radius19_checked,chord_keep%(7551,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,7],[(5,0),(16,7)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (7498,radius20,radius20_checked,chord_keep%(7552,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (7499,radius31,radius31_checked,chord_keep%(7553,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]),chord_close%(⟨[0,6],[(1,0),(5,6)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (7500,radius32,radius32_checked,chord_keep%(7554,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (7501,radius33,radius33_checked,chord_keep%(7555,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (7502,radius34,radius34_checked,chord_keep%(7556,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(2,0),(5,7)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (7503,radius35,radius35_checked,chord_keep%(7557,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(2,7)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (7504,radius36,radius36_checked,chord_keep%(7558,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (7505,radius37,radius37_checked,chord_keep%(7559,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(50,0),(1,7)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (7506,radius38,radius38_checked,chord_keep%(7560,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 6, .single 4, .single 8, .copy 14]),chord_close%(⟨[0,8],[(1,0),(5,8)]⟩))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (7507,radius39,radius39_checked,chord_keep%(7561,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(20,7)]⟩))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (7508,radius40,radius40_checked,chord_keep%(7562,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(5,7)]⟩))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (7509,radius41,radius41_checked,chord_keep%(7563,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (7510,radius42,radius42_checked,chord_keep%(7564,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (7511,radius43,radius43_checked,chord_keep%(7565,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(40,7)]⟩))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (7512,radius44,radius44_checked,chord_keep%(7566,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(1,0),(40,7)]⟩))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (7513,radius45,radius45_checked,chord_keep%(7567,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 6, .single 4, .single 8, .copy 14]),chord_close%(⟨[0,8],[(1,0),(5,8)]⟩))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (7514,radius46,radius46_checked,chord_keep%(7568,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 6, .single 4, .single 8, .copy 14]),chord_close%(⟨[0,8],[(1,0),(1,8)]⟩))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (7515,radius47,radius47_checked,chord_keep%(7569,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(2,0),(1,7)]⟩))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (7516,radius48,radius48_checked,chord_keep%(7570,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 5, .single 3, .single 7, .copy 13]),chord_close%(⟨[0,7],[(5,0),(1,7)]⟩))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (7517,radius49,radius49_checked,chord_keep%(7571,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(10,6)]⟩))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (7518,radius50,radius50_checked,chord_keep%(7572,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(2,0),(1,6)]⟩))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (7519,radius51,radius51_checked,chord_keep%(7573,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (7520,radius52,radius52_checked,chord_keep%(7574,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (7521,radius53,radius53_checked,chord_keep%(7575,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (7522,radius54,radius54_checked,chord_keep%(7576,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (7523,radius55,radius55_checked,chord_keep%(7577,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(20,0),(1,6)]⟩))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (7524,radius56,radius56_checked,chord_keep%(7578,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(2,0),(1,6)]⟩))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (7525,radius57,radius57_checked,chord_keep%(7579,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(2,6)]⟩))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (7526,radius58,radius58_checked,chord_keep%(7580,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(1,0),(1,6)]⟩))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (7527,radius59,radius59_checked,chord_keep%(7581,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(4,0),(1,6)]⟩))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (7528,radius60,radius60_checked,chord_keep%(7582,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,6],[(250,0),(1,6)]⟩))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (7529,radius61,radius61_checked,chord_keep%(7583,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 6, .copy 14]),chord_close%(⟨[0,6],[(4,0),(1,6)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (7530,radius62,radius62_checked,chord_keep%(7584,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 4, .single 2, .single 8, .copy 15]),chord_close%(⟨[0,8],[(1,0),(1,8)]⟩))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (7531,radius63,radius63_checked,chord_keep%(7585,[.single 1, .single 2, .single 3, .single 4, .pair 1 5, .single 0, .pair 1 9, .single 10, .single 10, .single 4, .single 2, .single 0, .copy 15]),chord_close%(⟨[0,7],[(1,0),(1,7)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout973Domain8_10Ids := by rfl
def outputIds : List (Fin poseCount) := [7532,7533,7534,7535,7536,7537,7538,7539,7540,7541,7542,7543,7544,7545,7546,7547,7548,7549,7550,7551,7552,7553,7554,7555,7556,7557,7558,7559,7560,7561,7562,7563,7564,7565,7566,7567,7568,7569,7570,7571,7572,7573,7574,7575,7576,7577,7578,7579,7580,7581,7582,7583,7584,7585]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout973Domain8_16Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout973Domain8_16Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout973Domain8_10 (q 0))
    (h0 : OrientedPoseCovered continuousScout973Domain3_13 (q 1))
    (h1 : OrientedPoseCovered continuousScout973Domain4_14 (q 2))
    (h2 : OrientedPoseCovered continuousScout973Domain11_0 (q 3))
    : OrientedPoseCovered continuousScout973Domain8_16 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout973Domain8_10Ids continuousScout973Domain8_16Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain3_13Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain4_14Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain11_0Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![2048,48,192,32768]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048)))
    (h0 : OrientedPoseCovered continuousScout973Domain3_13 (p.square (ownerIndex p 48)))
    (h1 : OrientedPoseCovered continuousScout973Domain4_14 (p.square (ownerIndex p 192)))
    (h2 : OrientedPoseCovered continuousScout973Domain11_0 (p.square (ownerIndex p 32768)))
    : OrientedPoseCovered continuousScout973Domain8_16 (p.square (ownerIndex p 2048)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout973Domain8_10 continuousScout973Domain8_16
    ![continuousScout973Domain3_13,continuousScout973Domain4_14,continuousScout973Domain11_0]
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
end N12Compact.Preservation.Chords.C973Step15

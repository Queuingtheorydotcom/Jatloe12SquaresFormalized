import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C973

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C973Step11
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C973

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := true
def lo : ℚ := (249262761/100000000)
def hi : ℚ := (249565723/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (7286,radius0,radius0_checked,[.single 2, .single 9])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (7287,radius1,radius1_checked,[.single 1, .single 8])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (7288,radius2,radius2_checked,[.single 1, .single 8])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (7289,radius3,radius3_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (7290,radius4,radius4_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (7291,radius5,radius5_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (7292,radius6,radius6_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (7293,radius7,radius7_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (7294,radius8,radius8_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (7295,radius9,radius9_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (7296,radius10,radius10_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (7297,radius11,radius11_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (7298,radius12,radius12_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (7299,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (7300,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (7301,radius15,radius15_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (7302,radius16,radius16_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (7303,radius17,radius17_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (7304,radius18,radius18_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (7305,radius19,radius19_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (7306,radius20,radius20_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (7307,radius21,radius21_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (7308,radius22,radius22_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (7309,radius23,radius23_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (7310,radius24,radius24_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (7311,radius25,radius25_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (7312,radius26,radius26_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (7313,radius27,radius27_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (7314,radius28,radius28_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (7315,radius29,radius29_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (7316,radius30,radius30_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (7317,radius31,radius31_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (7318,radius32,radius32_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (7319,radius33,radius33_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (7320,radius34,radius34_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (7321,radius35,radius35_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (7322,radius36,radius36_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (7323,radius37,radius37_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (7324,radius38,radius38_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (7325,radius39,radius39_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (7326,radius40,radius40_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (7327,radius41,radius41_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (7328,radius42,radius42_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (7329,radius43,radius43_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (7330,radius44,radius44_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor0_45 (dictionary,horizontal,lo,hi) := (7331,radius45,radius45_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_46 (dictionary,horizontal,lo,hi) := (7332,radius46,radius46_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_47 (dictionary,horizontal,lo,hi) := (7333,radius47,radius47_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_48 (dictionary,horizontal,lo,hi) := (7334,radius48,radius48_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor0_49 (dictionary,horizontal,lo,hi) := (7335,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_50 (dictionary,horizontal,lo,hi) := (7336,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_51 (dictionary,horizontal,lo,hi) := (7337,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_52 (dictionary,horizontal,lo,hi) := (7338,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor0_53 (dictionary,horizontal,lo,hi) := (7339,radius53,radius53_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor0_54 (dictionary,horizontal,lo,hi) := (7340,radius54,radius54_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor0_55 (dictionary,horizontal,lo,hi) := (7341,radius55,radius55_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor0_56 (dictionary,horizontal,lo,hi) := (7342,radius56,radius56_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor0_57 (dictionary,horizontal,lo,hi) := (7343,radius57,radius57_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor0_58 (dictionary,horizontal,lo,hi) := (7344,radius58,radius58_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor0_59 (dictionary,horizontal,lo,hi) := (7345,radius59,radius59_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor0_60 (dictionary,horizontal,lo,hi) := (7346,radius60,radius60_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor0_61 (dictionary,horizontal,lo,hi) := (7347,radius61,radius61_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor0_62 (dictionary,horizontal,lo,hi) := (7348,radius62,radius62_checked,[.single 3, .single 8])
checked_chord_neighbor neighbor0_63 (dictionary,horizontal,lo,hi) := (7349,radius63,radius63_checked,[.single 2, .single 9])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44, neighbor0_45, neighbor0_46, neighbor0_47,
    neighbor0_48, neighbor0_49, neighbor0_50, neighbor0_51, neighbor0_52, neighbor0_53, neighbor0_54, neighbor0_55, neighbor0_56, neighbor0_57, neighbor0_58, neighbor0_59,
    neighbor0_60, neighbor0_61, neighbor0_62, neighbor0_63]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout973Domain7_8Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (7478,radius0,radius0_checked,[.single 1, .single 8])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (7479,radius1,radius1_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (7480,radius2,radius2_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (7481,radius3,radius3_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (7482,radius4,radius4_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (7483,radius5,radius5_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (7484,radius6,radius6_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (7485,radius7,radius7_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (7486,radius8,radius8_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (7487,radius9,radius9_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (7488,radius10,radius10_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (7489,radius11,radius11_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (7490,radius12,radius12_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (7491,radius13,radius13_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (7492,radius14,radius14_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (7493,radius15,radius15_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (7494,radius16,radius16_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (7495,radius17,radius17_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (7496,radius18,radius18_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (7497,radius19,radius19_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (7498,radius20,radius20_checked,[.single 1, .single 6])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (7499,radius31,radius31_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (7500,radius32,radius32_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (7501,radius33,radius33_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (7502,radius34,radius34_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (7503,radius35,radius35_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (7504,radius36,radius36_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (7505,radius37,radius37_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (7506,radius38,radius38_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (7507,radius39,radius39_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (7508,radius40,radius40_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (7509,radius41,radius41_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (7510,radius42,radius42_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (7511,radius43,radius43_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (7512,radius44,radius44_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (7513,radius45,radius45_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (7514,radius46,radius46_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (7515,radius47,radius47_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (7516,radius48,radius48_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (7517,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (7518,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (7519,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (7520,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (7521,radius53,radius53_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (7522,radius54,radius54_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (7523,radius55,radius55_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (7524,radius56,radius56_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (7525,radius57,radius57_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (7526,radius58,radius58_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (7527,radius59,radius59_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (7528,radius60,radius60_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (7529,radius61,radius61_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (7530,radius62,radius62_checked,[.single 1, .single 7])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (7531,radius63,radius63_checked,[.single 1, .single 6])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout973Domain8_10Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (7755,radius0,radius0_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (7756,radius1,radius1_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (7757,radius2,radius2_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (7758,radius3,radius3_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (7759,radius4,radius4_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (7760,radius5,radius5_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (7761,radius6,radius6_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (7762,radius7,radius7_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (7763,radius8,radius8_checked,[.single 0, .single 5])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (7764,radius9,radius9_checked,[.single 0, .single 4])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (7765,radius10,radius10_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (7766,radius11,radius11_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (7767,radius12,radius12_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (7768,radius31,radius31_checked,[.single 2, .single 5])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (7769,radius32,radius32_checked,[.single 1, .single 4])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (7770,radius33,radius33_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (7771,radius34,radius34_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (7772,radius35,radius35_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (7773,radius36,radius36_checked,[.single 2, .single 6])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (7774,radius37,radius37_checked,[.single 3, .single 7])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (7775,radius38,radius38_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (7776,radius39,radius39_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (7777,radius40,radius40_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (7778,radius41,radius41_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (7779,radius42,radius42_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (7780,radius43,radius43_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (7781,radius44,radius44_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (7782,radius45,radius45_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (7783,radius46,radius46_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (7784,radius47,radius47_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (7785,radius48,radius48_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (7786,radius49,radius49_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (7787,radius50,radius50_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (7788,radius51,radius51_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (7789,radius52,radius52_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (7790,radius53,radius53_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (7791,radius54,radius54_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (7792,radius55,radius55_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (7793,radius56,radius56_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (7794,radius57,radius57_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (7795,radius58,radius58_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (7796,radius59,radius59_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (7797,radius60,radius60_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (7798,radius61,radius61_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (7799,radius62,radius62_checked,[.single 1, .single 5])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (7800,radius63,radius63_checked,[.single 1, .single 5])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout973Domain9_3Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (6430,radius0,radius0_checked,chord_close%(⟨[0,3],[(1,0),(2,3)]⟩),chord_keep%(6494,[.single 1, .pair 1 2, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (6431,radius1,radius1_checked,chord_close%(⟨[0,2],[(10,0),(1,2)]⟩),chord_keep%(6495,[.pair 1 5, .single 0, .single 4, .single 5, .single 6, .single 6, .single 4, .single 0, .single 5, .copy 11]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (6432,radius2,radius2_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(6496,[.pair 1 5, .single 0, .single 4, .single 5, .single 6, .single 6, .single 4, .single 0, .single 5, .copy 11]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (6433,radius3,radius3_checked,chord_close%(⟨[0,2],[(25,0),(2,2)]⟩),chord_keep%(6497,[.pair 1 5, .single 0, .single 4, .single 5, .single 6, .single 6, .single 4, .single 0, .single 5, .copy 11]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (6434,radius4,radius4_checked,chord_close%(⟨[0,2],[(1,0),(50,2)]⟩),chord_keep%(6498,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (6435,radius5,radius5_checked,chord_close%(⟨[0,2],[(1,0),(50,2)]⟩),chord_keep%(6499,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (6436,radius6,radius6_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6500,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (6437,radius7,radius7_checked,chord_close%(⟨[0,2],[(1,0),(25,2)]⟩),chord_keep%(6501,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (6438,radius8,radius8_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(6502,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (6439,radius9,radius9_checked,chord_close%(⟨[0,2],[(5,0),(2,2)]⟩),chord_keep%(6503,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (6440,radius10,radius10_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(6504,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (6441,radius11,radius11_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6505,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (6442,radius12,radius12_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6506,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (6443,radius13,radius13_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6507,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (6444,radius14,radius14_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(6508,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (6445,radius15,radius15_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(6509,[.single 0, .single 4, .single 5, .pair 4 6, .pair 0 6, .pair 0 6, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (6446,radius16,radius16_checked,chord_close%(⟨[0,2],[(1,0),(80,2)]⟩),chord_keep%(6510,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (6447,radius17,radius17_checked,chord_close%(⟨[0,2],[(1,0),(8,2)]⟩),chord_keep%(6511,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (6448,radius18,radius18_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6512,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (6449,radius19,radius19_checked,chord_close%(⟨[0,2],[(2,0),(5,2)]⟩),chord_keep%(6513,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (6450,radius20,radius20_checked,chord_close%(⟨[0,2],[(1,0),(25,2)]⟩),chord_keep%(6514,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (6451,radius21,radius21_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(6515,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (6452,radius22,radius22_checked,chord_close%(⟨[0,2],[(1,0),(80,2)]⟩),chord_keep%(6516,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (6453,radius23,radius23_checked,chord_close%(⟨[0,2],[(1,0),(5,2)]⟩),chord_keep%(6517,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (6454,radius24,radius24_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(6518,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (6455,radius25,radius25_checked,chord_close%(⟨[0,2],[(5,0),(1,2)]⟩),chord_keep%(6519,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (6456,radius26,radius26_checked,chord_close%(⟨[0,2],[(1,0),(1,2)]⟩),chord_keep%(6520,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (6457,radius27,radius27_checked,chord_close%(⟨[0,2],[(1,0),(4,2)]⟩),chord_keep%(6521,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (6458,radius28,radius28_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6522,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (6459,radius29,radius29_checked,chord_close%(⟨[0,2],[(1,0),(2,2)]⟩),chord_keep%(6523,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (6460,radius30,radius30_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6524,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (6461,radius31,radius31_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(6525,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (6462,radius32,radius32_checked,chord_close%(⟨[0,3],[(1,0),(2,3)]⟩),chord_keep%(6526,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (6463,radius33,radius33_checked,chord_close%(⟨[0,3],[(1,0),(2,3)]⟩),chord_keep%(6527,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (6464,radius34,radius34_checked,chord_close%(⟨[0,3],[(2,0),(5,3)]⟩),chord_keep%(6528,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (6465,radius35,radius35_checked,chord_close%(⟨[0,3],[(8,0),(5,3)]⟩),chord_keep%(6529,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (6466,radius36,radius36_checked,chord_close%(⟨[0,3],[(1,0),(125,3)]⟩),chord_keep%(6530,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (6467,radius37,radius37_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6531,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (6468,radius38,radius38_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6532,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (6469,radius39,radius39_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6533,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (6470,radius40,radius40_checked,chord_close%(⟨[0,3],[(5,0),(2,3)]⟩),chord_keep%(6534,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (6471,radius41,radius41_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6535,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (6472,radius42,radius42_checked,chord_close%(⟨[0,3],[(8,0),(1,3)]⟩),chord_keep%(6536,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (6473,radius43,radius43_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_keep%(6537,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (6474,radius44,radius44_checked,chord_close%(⟨[0,3],[(1,0),(50,3)]⟩),chord_keep%(6538,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (6475,radius45,radius45_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6539,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (6476,radius46,radius46_checked,chord_close%(⟨[0,3],[(1,0),(4,3)]⟩),chord_keep%(6540,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (6477,radius47,radius47_checked,chord_close%(⟨[0,3],[(20,0),(1,3)]⟩),chord_keep%(6541,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (6478,radius48,radius48_checked,chord_close%(⟨[0,3],[(1,0),(25,3)]⟩),chord_keep%(6542,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (6479,radius49,radius49_checked,chord_close%(⟨[0,3],[(5,0),(1,3)]⟩),chord_keep%(6543,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (6480,radius50,radius50_checked,chord_close%(⟨[0,3],[(2,0),(1,3)]⟩),chord_keep%(6544,[.single 0, .single 5, .single 6, .pair 5 7, .pair 0 7, .pair 0 7, .single 5, .single 0, .single 6, .copy 13]))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (6481,radius51,radius51_checked,chord_close%(⟨[0,4],[(1,0),(5,4)]⟩),chord_keep%(6545,[.pair 1 7, .single 0, .single 6, .single 7, .single 8, .single 8, .single 6, .single 0, .single 7, .copy 13]))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (6482,radius52,radius52_checked,chord_close%(⟨[0,4],[(2,0),(1,4)]⟩),chord_keep%(6546,[.pair 1 7, .single 0, .single 6, .single 7, .single 8, .single 8, .single 6, .single 0, .single 7, .copy 13]))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (6483,radius53,radius53_checked,chord_close%(⟨[0,4],[(1,0),(1,4)]⟩),chord_keep%(6547,[.pair 1 7, .single 0, .single 6, .single 7, .single 8, .single 8, .single 6, .single 0, .single 7, .copy 13]))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (6484,radius54,radius54_checked,chord_close%(⟨[0,4],[(1,0),(2,4)]⟩),chord_keep%(6548,[.pair 1 7, .single 0, .single 6, .single 7, .single 8, .single 8, .single 6, .single 0, .single 7, .copy 13]))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (6485,radius55,radius55_checked,chord_close%(⟨[0,4],[(2,0),(5,4)]⟩),chord_keep%(6549,[.pair 1 7, .single 0, .single 6, .single 7, .single 8, .single 8, .single 6, .single 0, .single 7, .copy 13]))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (6486,radius56,radius56_checked,chord_close%(⟨[0,3],[(8,0),(5,3)]⟩),chord_keep%(6550,[.pair 1 6, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (6487,radius57,radius57_checked,chord_close%(⟨[0,3],[(1,0),(5,3)]⟩),chord_keep%(6551,[.pair 1 6, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (6488,radius58,radius58_checked,chord_close%(⟨[0,3],[(1,0),(16,3)]⟩),chord_keep%(6552,[.pair 1 6, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (6489,radius59,radius59_checked,chord_close%(⟨[0,3],[(4,0),(25,3)]⟩),chord_keep%(6553,[.pair 1 6, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (6490,radius60,radius60_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6554,[.pair 1 6, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (6491,radius61,radius61_checked,chord_close%(⟨[0,3],[(4,0),(1,3)]⟩),chord_keep%(6555,[.pair 1 6, .single 0, .single 5, .single 6, .single 7, .single 7, .single 5, .single 0, .single 6, .copy 12]))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (6492,radius62,radius62_checked,chord_close%(⟨[0,3],[(1,0),(128,3)]⟩),chord_keep%(6556,[.pair 1 5, .single 0, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (6493,radius63,radius63_checked,chord_close%(⟨[0,3],[(1,0),(1,3)]⟩),chord_keep%(6557,[.pair 1 5, .single 0, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 0, .single 5, .copy 12]))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53, plan54, plan55, plan56, plan57, plan58, plan59,
    plan60, plan61, plan62, plan63]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout973Domain3_0Ids := by rfl
def outputIds : List (Fin poseCount) := [6494,6495,6496,6497,6498,6499,6500,6501,6502,6503,6504,6505,6506,6507,6508,6509,6510,6511,6512,6513,6514,6515,6516,6517,6518,6519,6520,6521,6522,6523,6524,6525,6526,6527,6528,6529,6530,6531,6532,6533,6534,6535,6536,6537,6538,6539,6540,6541,6542,6543,6544,6545,6546,6547,6548,6549,6550,6551,6552,6553,6554,6555,6556,6557]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout973Domain3_12Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout973Domain3_12Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout973Domain3_0 (q 0))
    (h0 : OrientedPoseCovered continuousScout973Domain7_8 (q 1))
    (h1 : OrientedPoseCovered continuousScout973Domain8_10 (q 2))
    (h2 : OrientedPoseCovered continuousScout973Domain9_3 (q 3))
    : OrientedPoseCovered continuousScout973Domain3_12 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout973Domain3_0Ids continuousScout973Domain3_12Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain7_8Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain8_10Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout973Domain9_3Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![48,1024,2048,4096]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout973Domain3_0 (p.square (ownerIndex p 48)))
    (h0 : OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)))
    (h1 : OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048)))
    (h2 : OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096)))
    : OrientedPoseCovered continuousScout973Domain3_12 (p.square (ownerIndex p 48)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout973Domain3_0 continuousScout973Domain3_12
    ![continuousScout973Domain7_8,continuousScout973Domain8_10,continuousScout973Domain9_3]
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
end N12Compact.Preservation.Chords.C973Step11

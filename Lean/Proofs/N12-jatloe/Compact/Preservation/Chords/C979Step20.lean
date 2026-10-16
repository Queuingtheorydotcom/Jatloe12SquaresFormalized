import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C979

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C979Step20
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C979

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (154296429/50000000)
def hi : ℚ := (317052689/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (9605,radius64,radius64_checked,[.single 6, .single 1])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (9606,radius65,radius65_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (9607,radius66,radius66_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (9608,radius67,radius67_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (9609,radius68,radius68_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (9610,radius69,radius69_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (9611,radius70,radius70_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (9612,radius71,radius71_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (9613,radius72,radius72_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (9614,radius73,radius73_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (9615,radius74,radius74_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (9616,radius75,radius75_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (9617,radius76,radius76_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (9618,radius77,radius77_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (9619,radius78,radius78_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (9620,radius79,radius79_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (9621,radius80,radius80_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (9622,radius81,radius81_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (9623,radius82,radius82_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (9624,radius83,radius83_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (9625,radius84,radius84_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (9626,radius85,radius85_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (9627,radius86,radius86_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (9628,radius87,radius87_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (9629,radius88,radius88_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (9630,radius89,radius89_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (9631,radius90,radius90_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (9632,radius91,radius91_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (9633,radius92,radius92_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (9634,radius93,radius93_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (9635,radius94,radius94_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (9636,radius95,radius95_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (9637,radius96,radius96_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (9638,radius97,radius97_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (9639,radius98,radius98_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (9640,radius99,radius99_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (9641,radius100,radius100_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (9642,radius101,radius101_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (9643,radius102,radius102_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (9644,radius103,radius103_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (9645,radius104,radius104_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (9646,radius105,radius105_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (9647,radius106,radius106_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (9648,radius107,radius107_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (9649,radius108,radius108_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_45 (dictionary,horizontal,lo,hi) := (9650,radius109,radius109_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_46 (dictionary,horizontal,lo,hi) := (9651,radius110,radius110_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_47 (dictionary,horizontal,lo,hi) := (9652,radius111,radius111_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_48 (dictionary,horizontal,lo,hi) := (9653,radius112,radius112_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_49 (dictionary,horizontal,lo,hi) := (9654,radius113,radius113_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_50 (dictionary,horizontal,lo,hi) := (9655,radius114,radius114_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_51 (dictionary,horizontal,lo,hi) := (9656,radius115,radius115_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_52 (dictionary,horizontal,lo,hi) := (9657,radius116,radius116_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_53 (dictionary,horizontal,lo,hi) := (9658,radius117,radius117_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_54 (dictionary,horizontal,lo,hi) := (9659,radius118,radius118_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_55 (dictionary,horizontal,lo,hi) := (9660,radius119,radius119_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_56 (dictionary,horizontal,lo,hi) := (9661,radius120,radius120_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_57 (dictionary,horizontal,lo,hi) := (9662,radius121,radius121_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_58 (dictionary,horizontal,lo,hi) := (9663,radius122,radius122_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_59 (dictionary,horizontal,lo,hi) := (9664,radius123,radius123_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_60 (dictionary,horizontal,lo,hi) := (9665,radius124,radius124_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_61 (dictionary,horizontal,lo,hi) := (9666,radius125,radius125_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_62 (dictionary,horizontal,lo,hi) := (9667,radius126,radius126_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_63 (dictionary,horizontal,lo,hi) := (9668,radius127,radius127_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_64 (dictionary,horizontal,lo,hi) := (9669,radius128,radius128_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_65 (dictionary,horizontal,lo,hi) := (9670,radius129,radius129_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_66 (dictionary,horizontal,lo,hi) := (9671,radius130,radius130_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_67 (dictionary,horizontal,lo,hi) := (9672,radius131,radius131_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_68 (dictionary,horizontal,lo,hi) := (9673,radius132,radius132_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_69 (dictionary,horizontal,lo,hi) := (9674,radius133,radius133_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor0_70 (dictionary,horizontal,lo,hi) := (9675,radius134,radius134_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_71 (dictionary,horizontal,lo,hi) := (9676,radius135,radius135_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_72 (dictionary,horizontal,lo,hi) := (9677,radius136,radius136_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_73 (dictionary,horizontal,lo,hi) := (9678,radius137,radius137_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_74 (dictionary,horizontal,lo,hi) := (9679,radius138,radius138_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_75 (dictionary,horizontal,lo,hi) := (9680,radius139,radius139_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_76 (dictionary,horizontal,lo,hi) := (9681,radius140,radius140_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_77 (dictionary,horizontal,lo,hi) := (9682,radius141,radius141_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_78 (dictionary,horizontal,lo,hi) := (9683,radius142,radius142_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_79 (dictionary,horizontal,lo,hi) := (9684,radius143,radius143_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_80 (dictionary,horizontal,lo,hi) := (9685,radius144,radius144_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_81 (dictionary,horizontal,lo,hi) := (9686,radius145,radius145_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_82 (dictionary,horizontal,lo,hi) := (9687,radius146,radius146_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_83 (dictionary,horizontal,lo,hi) := (9688,radius147,radius147_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_84 (dictionary,horizontal,lo,hi) := (9689,radius148,radius148_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_85 (dictionary,horizontal,lo,hi) := (9690,radius149,radius149_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_86 (dictionary,horizontal,lo,hi) := (9691,radius150,radius150_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_87 (dictionary,horizontal,lo,hi) := (9692,radius151,radius151_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_88 (dictionary,horizontal,lo,hi) := (9693,radius152,radius152_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_89 (dictionary,horizontal,lo,hi) := (9694,radius153,radius153_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_90 (dictionary,horizontal,lo,hi) := (9695,radius154,radius154_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_91 (dictionary,horizontal,lo,hi) := (9696,radius155,radius155_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_92 (dictionary,horizontal,lo,hi) := (9697,radius156,radius156_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_93 (dictionary,horizontal,lo,hi) := (9698,radius157,radius157_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_94 (dictionary,horizontal,lo,hi) := (9699,radius158,radius158_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_95 (dictionary,horizontal,lo,hi) := (9700,radius159,radius159_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_96 (dictionary,horizontal,lo,hi) := (9701,radius160,radius160_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_97 (dictionary,horizontal,lo,hi) := (9702,radius161,radius161_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_98 (dictionary,horizontal,lo,hi) := (9703,radius162,radius162_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_99 (dictionary,horizontal,lo,hi) := (9704,radius163,radius163_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_100 (dictionary,horizontal,lo,hi) := (9705,radius164,radius164_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_101 (dictionary,horizontal,lo,hi) := (9706,radius165,radius165_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_102 (dictionary,horizontal,lo,hi) := (9707,radius166,radius166_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_103 (dictionary,horizontal,lo,hi) := (9708,radius167,radius167_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_104 (dictionary,horizontal,lo,hi) := (9709,radius168,radius168_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_105 (dictionary,horizontal,lo,hi) := (9710,radius169,radius169_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_106 (dictionary,horizontal,lo,hi) := (9711,radius170,radius170_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_107 (dictionary,horizontal,lo,hi) := (9712,radius171,radius171_checked,[.single 4, .single 1])
checked_chord_neighbor neighbor0_108 (dictionary,horizontal,lo,hi) := (9713,radius172,radius172_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_109 (dictionary,horizontal,lo,hi) := (9714,radius173,radius173_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_110 (dictionary,horizontal,lo,hi) := (9715,radius174,radius174_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_111 (dictionary,horizontal,lo,hi) := (9716,radius175,radius175_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_112 (dictionary,horizontal,lo,hi) := (9717,radius176,radius176_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_113 (dictionary,horizontal,lo,hi) := (9718,radius177,radius177_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_114 (dictionary,horizontal,lo,hi) := (9719,radius178,radius178_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_115 (dictionary,horizontal,lo,hi) := (9720,radius179,radius179_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_116 (dictionary,horizontal,lo,hi) := (9721,radius180,radius180_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_117 (dictionary,horizontal,lo,hi) := (9722,radius181,radius181_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_118 (dictionary,horizontal,lo,hi) := (9723,radius182,radius182_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_119 (dictionary,horizontal,lo,hi) := (9724,radius183,radius183_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_120 (dictionary,horizontal,lo,hi) := (9725,radius184,radius184_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_121 (dictionary,horizontal,lo,hi) := (9726,radius185,radius185_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_122 (dictionary,horizontal,lo,hi) := (9727,radius186,radius186_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_123 (dictionary,horizontal,lo,hi) := (9728,radius187,radius187_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_124 (dictionary,horizontal,lo,hi) := (9729,radius188,radius188_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_125 (dictionary,horizontal,lo,hi) := (9730,radius189,radius189_checked,[.single 6, .single 1])
checked_chord_neighbor neighbor0_126 (dictionary,horizontal,lo,hi) := (9731,radius190,radius190_checked,[.single 6, .single 1])
checked_chord_neighbor neighbor0_127 (dictionary,horizontal,lo,hi) := (9732,radius191,radius191_checked,[.single 6, .single 1])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44, neighbor0_45, neighbor0_46, neighbor0_47,
    neighbor0_48, neighbor0_49, neighbor0_50, neighbor0_51, neighbor0_52, neighbor0_53, neighbor0_54, neighbor0_55, neighbor0_56, neighbor0_57, neighbor0_58, neighbor0_59,
    neighbor0_60, neighbor0_61, neighbor0_62, neighbor0_63, neighbor0_64, neighbor0_65, neighbor0_66, neighbor0_67, neighbor0_68, neighbor0_69, neighbor0_70, neighbor0_71,
    neighbor0_72, neighbor0_73, neighbor0_74, neighbor0_75, neighbor0_76, neighbor0_77, neighbor0_78, neighbor0_79, neighbor0_80, neighbor0_81, neighbor0_82, neighbor0_83,
    neighbor0_84, neighbor0_85, neighbor0_86, neighbor0_87, neighbor0_88, neighbor0_89, neighbor0_90, neighbor0_91, neighbor0_92, neighbor0_93, neighbor0_94, neighbor0_95,
    neighbor0_96, neighbor0_97, neighbor0_98, neighbor0_99, neighbor0_100, neighbor0_101, neighbor0_102, neighbor0_103, neighbor0_104, neighbor0_105, neighbor0_106, neighbor0_107,
    neighbor0_108, neighbor0_109, neighbor0_110, neighbor0_111, neighbor0_112, neighbor0_113, neighbor0_114, neighbor0_115, neighbor0_116, neighbor0_117, neighbor0_118, neighbor0_119,
    neighbor0_120, neighbor0_121, neighbor0_122, neighbor0_123, neighbor0_124, neighbor0_125, neighbor0_126, neighbor0_127]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout979Domain2_2Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (9861,radius64,radius64_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (9862,radius65,radius65_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (9863,radius66,radius66_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (9864,radius67,radius67_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (9865,radius68,radius68_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (9866,radius69,radius69_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (9867,radius70,radius70_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (9868,radius71,radius71_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (9869,radius72,radius72_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (9870,radius73,radius73_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (9871,radius74,radius74_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (9872,radius75,radius75_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (9873,radius76,radius76_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (9874,radius77,radius77_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (9875,radius78,radius78_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (9876,radius79,radius79_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (9877,radius80,radius80_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (9878,radius81,radius81_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (9879,radius82,radius82_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (9880,radius83,radius83_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (9881,radius84,radius84_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (9882,radius85,radius85_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (9883,radius86,radius86_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (9884,radius87,radius87_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (9885,radius88,radius88_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (9886,radius89,radius89_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (9887,radius90,radius90_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (9888,radius91,radius91_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (9889,radius92,radius92_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (9890,radius93,radius93_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (9891,radius94,radius94_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (9892,radius95,radius95_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (9893,radius96,radius96_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (9894,radius97,radius97_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (9895,radius98,radius98_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (9896,radius132,radius132_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (9897,radius133,radius133_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (9898,radius134,radius134_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (9899,radius135,radius135_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (9900,radius136,radius136_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (9901,radius137,radius137_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (9902,radius138,radius138_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (9903,radius139,radius139_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (9904,radius140,radius140_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (9905,radius141,radius141_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (9906,radius142,radius142_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (9907,radius143,radius143_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (9908,radius144,radius144_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (9909,radius145,radius145_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (9910,radius146,radius146_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (9911,radius147,radius147_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (9912,radius148,radius148_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (9913,radius149,radius149_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (9914,radius150,radius150_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (9915,radius151,radius151_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (9916,radius152,radius152_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (9917,radius153,radius153_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (9918,radius154,radius154_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (9919,radius155,radius155_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (9920,radius156,radius156_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (9921,radius157,radius157_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_61 (dictionary,horizontal,lo,hi) := (9922,radius158,radius158_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_62 (dictionary,horizontal,lo,hi) := (9923,radius159,radius159_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_63 (dictionary,horizontal,lo,hi) := (9924,radius160,radius160_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_64 (dictionary,horizontal,lo,hi) := (9925,radius161,radius161_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_65 (dictionary,horizontal,lo,hi) := (9926,radius162,radius162_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_66 (dictionary,horizontal,lo,hi) := (9927,radius163,radius163_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_67 (dictionary,horizontal,lo,hi) := (9928,radius164,radius164_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_68 (dictionary,horizontal,lo,hi) := (9929,radius165,radius165_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_69 (dictionary,horizontal,lo,hi) := (9930,radius166,radius166_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_70 (dictionary,horizontal,lo,hi) := (9931,radius167,radius167_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_71 (dictionary,horizontal,lo,hi) := (9932,radius168,radius168_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_72 (dictionary,horizontal,lo,hi) := (9933,radius169,radius169_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_73 (dictionary,horizontal,lo,hi) := (9934,radius170,radius170_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_74 (dictionary,horizontal,lo,hi) := (9935,radius171,radius171_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_75 (dictionary,horizontal,lo,hi) := (9936,radius172,radius172_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_76 (dictionary,horizontal,lo,hi) := (9937,radius173,radius173_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_77 (dictionary,horizontal,lo,hi) := (9938,radius174,radius174_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_78 (dictionary,horizontal,lo,hi) := (9939,radius175,radius175_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_79 (dictionary,horizontal,lo,hi) := (9940,radius176,radius176_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_80 (dictionary,horizontal,lo,hi) := (9941,radius177,radius177_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_81 (dictionary,horizontal,lo,hi) := (9942,radius178,radius178_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_82 (dictionary,horizontal,lo,hi) := (9943,radius179,radius179_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_83 (dictionary,horizontal,lo,hi) := (9944,radius180,radius180_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_84 (dictionary,horizontal,lo,hi) := (9945,radius181,radius181_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_85 (dictionary,horizontal,lo,hi) := (9946,radius182,radius182_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_86 (dictionary,horizontal,lo,hi) := (9947,radius183,radius183_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_87 (dictionary,horizontal,lo,hi) := (9948,radius184,radius184_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_88 (dictionary,horizontal,lo,hi) := (9949,radius185,radius185_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_89 (dictionary,horizontal,lo,hi) := (9950,radius186,radius186_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_90 (dictionary,horizontal,lo,hi) := (9951,radius187,radius187_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_91 (dictionary,horizontal,lo,hi) := (9952,radius188,radius188_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_92 (dictionary,horizontal,lo,hi) := (9953,radius189,radius189_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_93 (dictionary,horizontal,lo,hi) := (9954,radius190,radius190_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_94 (dictionary,horizontal,lo,hi) := (9955,radius191,radius191_checked,[.single 5, .single 2])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53, neighbor1_54, neighbor1_55, neighbor1_56, neighbor1_57, neighbor1_58, neighbor1_59,
    neighbor1_60, neighbor1_61, neighbor1_62, neighbor1_63, neighbor1_64, neighbor1_65, neighbor1_66, neighbor1_67, neighbor1_68, neighbor1_69, neighbor1_70, neighbor1_71,
    neighbor1_72, neighbor1_73, neighbor1_74, neighbor1_75, neighbor1_76, neighbor1_77, neighbor1_78, neighbor1_79, neighbor1_80, neighbor1_81, neighbor1_82, neighbor1_83,
    neighbor1_84, neighbor1_85, neighbor1_86, neighbor1_87, neighbor1_88, neighbor1_89, neighbor1_90, neighbor1_91, neighbor1_92, neighbor1_93, neighbor1_94]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout979Domain3_20Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (8801,radius64,radius64_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (8802,radius65,radius65_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (8803,radius66,radius66_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (8804,radius67,radius67_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (8805,radius68,radius68_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (8806,radius69,radius69_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (8807,radius70,radius70_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (8808,radius71,radius71_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (8809,radius72,radius72_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (8810,radius73,radius73_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (8811,radius74,radius74_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (8812,radius75,radius75_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (8813,radius76,radius76_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (8814,radius77,radius77_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (8815,radius78,radius78_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (8816,radius79,radius79_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (8817,radius80,radius80_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (8818,radius81,radius81_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (8819,radius82,radius82_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (8820,radius83,radius83_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (8821,radius84,radius84_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (8822,radius85,radius85_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (8823,radius86,radius86_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (8824,radius87,radius87_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (8825,radius88,radius88_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (8826,radius89,radius89_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (8827,radius90,radius90_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (8828,radius91,radius91_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (8829,radius92,radius92_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (8830,radius93,radius93_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (8831,radius94,radius94_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (8832,radius95,radius95_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (8833,radius96,radius96_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (8834,radius97,radius97_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (8835,radius98,radius98_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (8836,radius99,radius99_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (8837,radius100,radius100_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (8838,radius101,radius101_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (8839,radius102,radius102_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (8840,radius103,radius103_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (8841,radius104,radius104_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (8842,radius105,radius105_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (8843,radius106,radius106_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (8844,radius107,radius107_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (8845,radius108,radius108_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (8846,radius109,radius109_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (8847,radius110,radius110_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (8848,radius111,radius111_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (8849,radius112,radius112_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (8850,radius113,radius113_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (8851,radius114,radius114_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (8852,radius115,radius115_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_52 (dictionary,horizontal,lo,hi) := (8853,radius116,radius116_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_53 (dictionary,horizontal,lo,hi) := (8854,radius117,radius117_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_54 (dictionary,horizontal,lo,hi) := (8855,radius118,radius118_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_55 (dictionary,horizontal,lo,hi) := (8856,radius119,radius119_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_56 (dictionary,horizontal,lo,hi) := (8857,radius120,radius120_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_57 (dictionary,horizontal,lo,hi) := (8858,radius121,radius121_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_58 (dictionary,horizontal,lo,hi) := (8859,radius122,radius122_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_59 (dictionary,horizontal,lo,hi) := (8860,radius123,radius123_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_60 (dictionary,horizontal,lo,hi) := (8861,radius124,radius124_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_61 (dictionary,horizontal,lo,hi) := (8862,radius125,radius125_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_62 (dictionary,horizontal,lo,hi) := (8863,radius126,radius126_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_63 (dictionary,horizontal,lo,hi) := (8864,radius127,radius127_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_64 (dictionary,horizontal,lo,hi) := (8865,radius128,radius128_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_65 (dictionary,horizontal,lo,hi) := (8866,radius129,radius129_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_66 (dictionary,horizontal,lo,hi) := (8867,radius130,radius130_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_67 (dictionary,horizontal,lo,hi) := (8868,radius131,radius131_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_68 (dictionary,horizontal,lo,hi) := (8869,radius132,radius132_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_69 (dictionary,horizontal,lo,hi) := (8870,radius133,radius133_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_70 (dictionary,horizontal,lo,hi) := (8871,radius134,radius134_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_71 (dictionary,horizontal,lo,hi) := (8872,radius135,radius135_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_72 (dictionary,horizontal,lo,hi) := (8873,radius136,radius136_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_73 (dictionary,horizontal,lo,hi) := (8874,radius137,radius137_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_74 (dictionary,horizontal,lo,hi) := (8875,radius138,radius138_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_75 (dictionary,horizontal,lo,hi) := (8876,radius139,radius139_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_76 (dictionary,horizontal,lo,hi) := (8877,radius140,radius140_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_77 (dictionary,horizontal,lo,hi) := (8878,radius141,radius141_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_78 (dictionary,horizontal,lo,hi) := (8879,radius142,radius142_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_79 (dictionary,horizontal,lo,hi) := (8880,radius143,radius143_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_80 (dictionary,horizontal,lo,hi) := (8881,radius144,radius144_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_81 (dictionary,horizontal,lo,hi) := (8882,radius145,radius145_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_82 (dictionary,horizontal,lo,hi) := (8883,radius146,radius146_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_83 (dictionary,horizontal,lo,hi) := (8884,radius147,radius147_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_84 (dictionary,horizontal,lo,hi) := (8885,radius148,radius148_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_85 (dictionary,horizontal,lo,hi) := (8886,radius149,radius149_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_86 (dictionary,horizontal,lo,hi) := (8887,radius150,radius150_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_87 (dictionary,horizontal,lo,hi) := (8888,radius151,radius151_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_88 (dictionary,horizontal,lo,hi) := (8889,radius152,radius152_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_89 (dictionary,horizontal,lo,hi) := (8890,radius153,radius153_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_90 (dictionary,horizontal,lo,hi) := (8891,radius154,radius154_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_91 (dictionary,horizontal,lo,hi) := (8892,radius155,radius155_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_92 (dictionary,horizontal,lo,hi) := (8893,radius156,radius156_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_93 (dictionary,horizontal,lo,hi) := (8894,radius157,radius157_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_94 (dictionary,horizontal,lo,hi) := (8895,radius158,radius158_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_95 (dictionary,horizontal,lo,hi) := (8896,radius159,radius159_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_96 (dictionary,horizontal,lo,hi) := (8897,radius160,radius160_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_97 (dictionary,horizontal,lo,hi) := (8898,radius161,radius161_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_98 (dictionary,horizontal,lo,hi) := (8899,radius162,radius162_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_99 (dictionary,horizontal,lo,hi) := (8900,radius163,radius163_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_100 (dictionary,horizontal,lo,hi) := (8901,radius164,radius164_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_101 (dictionary,horizontal,lo,hi) := (8902,radius165,radius165_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_102 (dictionary,horizontal,lo,hi) := (8903,radius166,radius166_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_103 (dictionary,horizontal,lo,hi) := (8904,radius167,radius167_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_104 (dictionary,horizontal,lo,hi) := (8905,radius168,radius168_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_105 (dictionary,horizontal,lo,hi) := (8906,radius169,radius169_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_106 (dictionary,horizontal,lo,hi) := (8907,radius170,radius170_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_107 (dictionary,horizontal,lo,hi) := (8908,radius171,radius171_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_108 (dictionary,horizontal,lo,hi) := (8909,radius172,radius172_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_109 (dictionary,horizontal,lo,hi) := (8910,radius173,radius173_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_110 (dictionary,horizontal,lo,hi) := (8911,radius174,radius174_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_111 (dictionary,horizontal,lo,hi) := (8912,radius175,radius175_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_112 (dictionary,horizontal,lo,hi) := (8913,radius176,radius176_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_113 (dictionary,horizontal,lo,hi) := (8914,radius177,radius177_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_114 (dictionary,horizontal,lo,hi) := (8915,radius178,radius178_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_115 (dictionary,horizontal,lo,hi) := (8916,radius179,radius179_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_116 (dictionary,horizontal,lo,hi) := (8917,radius180,radius180_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_117 (dictionary,horizontal,lo,hi) := (8918,radius181,radius181_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_118 (dictionary,horizontal,lo,hi) := (8919,radius182,radius182_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_119 (dictionary,horizontal,lo,hi) := (8920,radius183,radius183_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_120 (dictionary,horizontal,lo,hi) := (8921,radius184,radius184_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_121 (dictionary,horizontal,lo,hi) := (8922,radius185,radius185_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_122 (dictionary,horizontal,lo,hi) := (8923,radius186,radius186_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_123 (dictionary,horizontal,lo,hi) := (8924,radius187,radius187_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_124 (dictionary,horizontal,lo,hi) := (8925,radius188,radius188_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_125 (dictionary,horizontal,lo,hi) := (8926,radius189,radius189_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_126 (dictionary,horizontal,lo,hi) := (8927,radius190,radius190_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_127 (dictionary,horizontal,lo,hi) := (8928,radius191,radius191_checked,[.single 8, .single 3])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28, neighbor2_29, neighbor2_30, neighbor2_31, neighbor2_32, neighbor2_33, neighbor2_34, neighbor2_35,
    neighbor2_36, neighbor2_37, neighbor2_38, neighbor2_39, neighbor2_40, neighbor2_41, neighbor2_42, neighbor2_43, neighbor2_44, neighbor2_45, neighbor2_46, neighbor2_47,
    neighbor2_48, neighbor2_49, neighbor2_50, neighbor2_51, neighbor2_52, neighbor2_53, neighbor2_54, neighbor2_55, neighbor2_56, neighbor2_57, neighbor2_58, neighbor2_59,
    neighbor2_60, neighbor2_61, neighbor2_62, neighbor2_63, neighbor2_64, neighbor2_65, neighbor2_66, neighbor2_67, neighbor2_68, neighbor2_69, neighbor2_70, neighbor2_71,
    neighbor2_72, neighbor2_73, neighbor2_74, neighbor2_75, neighbor2_76, neighbor2_77, neighbor2_78, neighbor2_79, neighbor2_80, neighbor2_81, neighbor2_82, neighbor2_83,
    neighbor2_84, neighbor2_85, neighbor2_86, neighbor2_87, neighbor2_88, neighbor2_89, neighbor2_90, neighbor2_91, neighbor2_92, neighbor2_93, neighbor2_94, neighbor2_95,
    neighbor2_96, neighbor2_97, neighbor2_98, neighbor2_99, neighbor2_100, neighbor2_101, neighbor2_102, neighbor2_103, neighbor2_104, neighbor2_105, neighbor2_106, neighbor2_107,
    neighbor2_108, neighbor2_109, neighbor2_110, neighbor2_111, neighbor2_112, neighbor2_113, neighbor2_114, neighbor2_115, neighbor2_116, neighbor2_117, neighbor2_118, neighbor2_119,
    neighbor2_120, neighbor2_121, neighbor2_122, neighbor2_123, neighbor2_124, neighbor2_125, neighbor2_126, neighbor2_127]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout979Domain10_0Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (11121,radius64,radius64_checked,chord_keep%(11244,[.single 1, .single 2, .pair 1 3, .single 0, .pair 0 9, .pair 1 9, .single 10, .single 10, .single 0, .single 2, .pair 0 9, .copy 15]),chord_close%(⟨[0,5],[(2,0),(5,5)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (11122,radius65,radius65_checked,chord_keep%(11245,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (11123,radius66,radius66_checked,chord_keep%(11246,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(4,0),(1,5)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (11124,radius67,radius67_checked,chord_keep%(11247,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(80,0),(1,5)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (11125,radius68,radius68_checked,chord_keep%(11248,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (11126,radius69,radius69_checked,chord_keep%(11249,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (11127,radius70,radius70_checked,chord_keep%(11250,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (11128,radius71,radius71_checked,chord_keep%(11251,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(400,0),(1,4)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (11129,radius72,radius72_checked,chord_keep%(11252,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (11130,radius73,radius73_checked,chord_keep%(11253,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(2,0),(1,5)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (11131,radius74,radius74_checked,chord_keep%(11254,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(32,5)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (11132,radius75,radius75_checked,chord_keep%(11255,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(5,5)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (11133,radius76,radius76_checked,chord_keep%(11256,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (11134,radius77,radius77_checked,chord_keep%(11257,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (11135,radius78,radius78_checked,chord_keep%(11258,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (11136,radius79,radius79_checked,chord_keep%(11259,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (11137,radius80,radius80_checked,chord_keep%(11260,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (11138,radius81,radius81_checked,chord_keep%(11261,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (11139,radius82,radius82_checked,chord_keep%(11262,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (11140,radius83,radius83_checked,chord_keep%(11263,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(20,0),(1,4)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (11141,radius84,radius84_checked,chord_keep%(11264,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 10, .single 5, .single 3, .single 8, .copy 15]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (11142,radius85,radius85_checked,chord_keep%(11265,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 3, .single 7, .copy 14]),chord_close%(⟨[0,5],[(5,0),(1,5)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (11143,radius86,radius86_checked,chord_keep%(11266,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 5, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (11144,radius87,radius87_checked,chord_keep%(11267,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (11145,radius88,radius88_checked,chord_keep%(11268,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (11146,radius89,radius89_checked,chord_keep%(11269,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (11147,radius90,radius90_checked,chord_keep%(11270,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (11148,radius91,radius91_checked,chord_keep%(11271,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (11149,radius92,radius92_checked,chord_keep%(11272,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (11150,radius93,radius93_checked,chord_keep%(11273,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(32,0),(1,4)]⟩))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (11151,radius94,radius94_checked,chord_keep%(11274,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (11152,radius95,radius95_checked,chord_keep%(11275,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (11153,radius96,radius96_checked,chord_keep%(11276,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (11154,radius97,radius97_checked,chord_keep%(11277,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (11155,radius98,radius98_checked,chord_keep%(11278,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (11156,radius99,radius99_checked,chord_keep%(11279,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (11157,radius100,radius100_checked,chord_keep%(11280,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (11158,radius101,radius101_checked,chord_keep%(11281,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (11159,radius102,radius102_checked,chord_keep%(11282,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(64,0),(5,3)]⟩))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (11160,radius103,radius103_checked,chord_keep%(11283,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (11161,radius104,radius104_checked,chord_keep%(11284,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (11162,radius105,radius105_checked,chord_keep%(11285,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(5,0),(256,3)]⟩))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (11163,radius106,radius106_checked,chord_keep%(11286,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (11164,radius107,radius107_checked,chord_keep%(11287,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (11165,radius108,radius108_checked,chord_keep%(11288,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(10,3)]⟩))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (11166,radius109,radius109_checked,chord_keep%(11289,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (11167,radius110,radius110_checked,chord_keep%(11290,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (11168,radius114,radius114_checked,chord_keep%(11291,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(4,3)]⟩))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (11169,radius115,radius115_checked,chord_keep%(11292,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(10,0),(1,3)]⟩))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (11170,radius116,radius116_checked,chord_keep%(11293,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (11171,radius117,radius117_checked,chord_keep%(11294,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (11172,radius118,radius118_checked,chord_keep%(11295,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (11173,radius119,radius119_checked,chord_keep%(11296,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (11174,radius120,radius120_checked,chord_keep%(11297,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(8,3)]⟩))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (11175,radius121,radius121_checked,chord_keep%(11298,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(40,3)]⟩))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (11176,radius122,radius122_checked,chord_keep%(11299,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (11177,radius123,radius123_checked,chord_keep%(11300,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(640,3)]⟩))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (11178,radius124,radius124_checked,chord_keep%(11301,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(4,3)]⟩))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (11179,radius125,radius125_checked,chord_keep%(11302,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(5,0),(1,3)]⟩))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (11180,radius126,radius126_checked,chord_keep%(11303,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (11181,radius127,radius127_checked,chord_keep%(11304,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(20,3)]⟩))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (11182,radius128,radius128_checked,chord_keep%(11305,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (11183,radius129,radius129_checked,chord_keep%(11306,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (11184,radius130,radius130_checked,chord_keep%(11307,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(16,0),(1,3)]⟩))
checked_chord_plan plan64 (dictionary,horizontal,lo,hi) := (11185,radius131,radius131_checked,chord_keep%(11308,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(8,0),(1,3)]⟩))
checked_chord_plan plan65 (dictionary,horizontal,lo,hi) := (11186,radius132,radius132_checked,chord_keep%(11309,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan66 (dictionary,horizontal,lo,hi) := (11187,radius133,radius133_checked,chord_keep%(11310,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan67 (dictionary,horizontal,lo,hi) := (11188,radius134,radius134_checked,chord_keep%(11311,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan68 (dictionary,horizontal,lo,hi) := (11189,radius135,radius135_checked,chord_keep%(11312,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan69 (dictionary,horizontal,lo,hi) := (11190,radius136,radius136_checked,chord_keep%(11313,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan70 (dictionary,horizontal,lo,hi) := (11191,radius137,radius137_checked,chord_keep%(11314,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan71 (dictionary,horizontal,lo,hi) := (11192,radius138,radius138_checked,chord_keep%(11315,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan72 (dictionary,horizontal,lo,hi) := (11193,radius139,radius139_checked,chord_keep%(11316,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(25,0),(1,4)]⟩))
checked_chord_plan plan73 (dictionary,horizontal,lo,hi) := (11194,radius140,radius140_checked,chord_keep%(11317,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan74 (dictionary,horizontal,lo,hi) := (11195,radius141,radius141_checked,chord_keep%(11318,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan75 (dictionary,horizontal,lo,hi) := (11196,radius142,radius142_checked,chord_keep%(11319,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan76 (dictionary,horizontal,lo,hi) := (11197,radius143,radius143_checked,chord_keep%(11320,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(5,0),(2,4)]⟩))
checked_chord_plan plan77 (dictionary,horizontal,lo,hi) := (11198,radius144,radius144_checked,chord_keep%(11321,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan78 (dictionary,horizontal,lo,hi) := (11199,radius145,radius145_checked,chord_keep%(11322,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan79 (dictionary,horizontal,lo,hi) := (11200,radius146,radius146_checked,chord_keep%(11323,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan80 (dictionary,horizontal,lo,hi) := (11201,radius147,radius147_checked,chord_keep%(11324,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan81 (dictionary,horizontal,lo,hi) := (11202,radius148,radius148_checked,chord_keep%(11325,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan82 (dictionary,horizontal,lo,hi) := (11203,radius149,radius149_checked,chord_keep%(11326,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan83 (dictionary,horizontal,lo,hi) := (11204,radius150,radius150_checked,chord_keep%(11327,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan84 (dictionary,horizontal,lo,hi) := (11205,radius151,radius151_checked,chord_keep%(11328,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan85 (dictionary,horizontal,lo,hi) := (11206,radius152,radius152_checked,chord_keep%(11329,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan86 (dictionary,horizontal,lo,hi) := (11207,radius153,radius153_checked,chord_keep%(11330,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan87 (dictionary,horizontal,lo,hi) := (11208,radius154,radius154_checked,chord_keep%(11331,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan88 (dictionary,horizontal,lo,hi) := (11209,radius155,radius155_checked,chord_keep%(11332,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan89 (dictionary,horizontal,lo,hi) := (11210,radius156,radius156_checked,chord_keep%(11333,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(64,4)]⟩))
checked_chord_plan plan90 (dictionary,horizontal,lo,hi) := (11211,radius157,radius157_checked,chord_keep%(11334,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan91 (dictionary,horizontal,lo,hi) := (11212,radius158,radius158_checked,chord_keep%(11335,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan92 (dictionary,horizontal,lo,hi) := (11213,radius159,radius159_checked,chord_keep%(11336,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan93 (dictionary,horizontal,lo,hi) := (11214,radius160,radius160_checked,chord_keep%(11337,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan94 (dictionary,horizontal,lo,hi) := (11215,radius161,radius161_checked,chord_keep%(11338,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(50,4)]⟩))
checked_chord_plan plan95 (dictionary,horizontal,lo,hi) := (11216,radius162,radius162_checked,chord_keep%(11339,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan96 (dictionary,horizontal,lo,hi) := (11217,radius163,radius163_checked,chord_keep%(11340,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan97 (dictionary,horizontal,lo,hi) := (11218,radius164,radius164_checked,chord_keep%(11341,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 5, .copy 12]),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan98 (dictionary,horizontal,lo,hi) := (11219,radius167,radius167_checked,chord_keep%(11342,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan99 (dictionary,horizontal,lo,hi) := (11220,radius168,radius168_checked,chord_keep%(11343,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan100 (dictionary,horizontal,lo,hi) := (11221,radius169,radius169_checked,chord_keep%(11344,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan101 (dictionary,horizontal,lo,hi) := (11222,radius170,radius170_checked,chord_keep%(11345,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan102 (dictionary,horizontal,lo,hi) := (11223,radius171,radius171_checked,chord_keep%(11346,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(16,4)]⟩))
checked_chord_plan plan103 (dictionary,horizontal,lo,hi) := (11224,radius172,radius172_checked,chord_keep%(11347,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan104 (dictionary,horizontal,lo,hi) := (11225,radius173,radius173_checked,chord_keep%(11348,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan105 (dictionary,horizontal,lo,hi) := (11226,radius174,radius174_checked,chord_keep%(11349,[.single 1, .single 2, .pair 1 3, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .single 0, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan106 (dictionary,horizontal,lo,hi) := (11227,radius175,radius175_checked,chord_keep%(11350,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .single 0, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(4,0),(5,5)]⟩))
checked_chord_plan plan107 (dictionary,horizontal,lo,hi) := (11228,radius176,radius176_checked,chord_keep%(11351,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .single 0, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(100,5)]⟩))
checked_chord_plan plan108 (dictionary,horizontal,lo,hi) := (11229,radius177,radius177_checked,chord_keep%(11352,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .single 0, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(16,0),(1,5)]⟩))
checked_chord_plan plan109 (dictionary,horizontal,lo,hi) := (11230,radius178,radius178_checked,chord_keep%(11353,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 10, .single 10, .single 0, .single 2, .single 7, .copy 15]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan110 (dictionary,horizontal,lo,hi) := (11231,radius179,radius179_checked,chord_keep%(11354,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 10, .single 10, .single 0, .single 2, .single 7, .copy 15]),chord_close%(⟨[0,5],[(8,0),(1,5)]⟩))
checked_chord_plan plan111 (dictionary,horizontal,lo,hi) := (11232,radius180,radius180_checked,chord_keep%(11355,[.single 1, .single 2, .single 3, .pair 1 4, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 10, .single 10, .single 0, .single 2, .single 7, .copy 15]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan112 (dictionary,horizontal,lo,hi) := (11233,radius181,radius181_checked,chord_keep%(11356,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan113 (dictionary,horizontal,lo,hi) := (11234,radius182,radius182_checked,chord_keep%(11357,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan114 (dictionary,horizontal,lo,hi) := (11235,radius183,radius183_checked,chord_keep%(11358,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan115 (dictionary,horizontal,lo,hi) := (11236,radius184,radius184_checked,chord_keep%(11359,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(4,0),(5,4)]⟩))
checked_chord_plan plan116 (dictionary,horizontal,lo,hi) := (11237,radius185,radius185_checked,chord_keep%(11360,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(256,0),(1,4)]⟩))
checked_chord_plan plan117 (dictionary,horizontal,lo,hi) := (11238,radius186,radius186_checked,chord_keep%(11361,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan118 (dictionary,horizontal,lo,hi) := (11239,radius187,radius187_checked,chord_keep%(11362,[.pair 1 6, .pair 0 1, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 9, .single 9, .single 0, .pair 0 1, .pair 0 7, .copy 14]),chord_close%(⟨[0,4],[(20,0),(1,4)]⟩))
checked_chord_plan plan119 (dictionary,horizontal,lo,hi) := (11240,radius188,radius188_checked,chord_keep%(11363,[.pair 1 7, .pair 0 1, .single 0, .pair 0 8, .pair 1 8, .single 9, .single 10, .single 10, .single 0, .pair 0 1, .pair 0 8, .copy 15]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan120 (dictionary,horizontal,lo,hi) := (11241,radius189,radius189_checked,chord_keep%(11364,[.pair 1 7, .pair 0 1, .single 0, .pair 0 8, .pair 1 8, .single 9, .single 10, .single 10, .single 0, .pair 0 1, .pair 0 8, .copy 15]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan121 (dictionary,horizontal,lo,hi) := (11242,radius190,radius190_checked,chord_keep%(11365,[.single 1, .single 2, .pair 1 3, .single 0, .pair 0 8, .pair 1 8, .single 9, .single 10, .single 10, .single 0, .single 2, .pair 0 8, .copy 15]),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan122 (dictionary,horizontal,lo,hi) := (11243,radius191,radius191_checked,chord_keep%(11366,[.single 1, .single 2, .pair 1 3, .single 0, .pair 0 8, .pair 1 8, .single 9, .single 10, .single 10, .single 0, .single 2, .pair 0 8, .copy 15]),chord_close%(⟨[0,5],[(4,0),(1,5)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35,
    plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47,
    plan48, plan49, plan50, plan51, plan52, plan53, plan54, plan55, plan56, plan57, plan58, plan59,
    plan60, plan61, plan62, plan63, plan64, plan65, plan66, plan67, plan68, plan69, plan70, plan71,
    plan72, plan73, plan74, plan75, plan76, plan77, plan78, plan79, plan80, plan81, plan82, plan83,
    plan84, plan85, plan86, plan87, plan88, plan89, plan90, plan91, plan92, plan93, plan94, plan95,
    plan96, plan97, plan98, plan99, plan100, plan101, plan102, plan103, plan104, plan105, plan106, plan107,
    plan108, plan109, plan110, plan111, plan112, plan113, plan114, plan115, plan116, plan117, plan118, plan119,
    plan120, plan121, plan122]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout979Domain6_13Ids := by rfl
def outputIds : List (Fin poseCount) := [11244,11245,11246,11247,11248,11249,11250,11251,11252,11253,11254,11255,11256,11257,11258,11259,11260,11261,11262,11263,11264,11265,11266,11267,11268,11269,11270,11271,11272,11273,11274,11275,11276,11277,11278,11279,11280,11281,11282,11283,11284,11285,11286,11287,11288,11289,11290,11291,11292,11293,11294,11295,11296,11297,11298,11299,11300,11301,11302,11303,11304,11305,11306,11307,11308,11309,11310,11311,11312,11313,11314,11315,11316,11317,11318,11319,11320,11321,11322,11323,11324,11325,11326,11327,11328,11329,11330,11331,11332,11333,11334,11335,11336,11337,11338,11339,11340,11341,11342,11343,11344,11345,11346,11347,11348,11349,11350,11351,11352,11353,11354,11355,11356,11357,11358,11359,11360,11361,11362,11363,11364,11365,11366]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout979Domain6_21Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout979Domain6_21Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout979Domain6_13 (q 0))
    (h0 : OrientedPoseCovered continuousScout979Domain2_2 (q 1))
    (h1 : OrientedPoseCovered continuousScout979Domain3_20 (q 2))
    (h2 : OrientedPoseCovered continuousScout979Domain10_0 (q 3))
    : OrientedPoseCovered continuousScout979Domain6_21 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout979Domain6_13Ids continuousScout979Domain6_21Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain2_2Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain3_20Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain10_0Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![512,12,48,16384]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout979Domain6_13 (p.square (ownerIndex p 512)))
    (h0 : OrientedPoseCovered continuousScout979Domain2_2 (p.square (ownerIndex p 12)))
    (h1 : OrientedPoseCovered continuousScout979Domain3_20 (p.square (ownerIndex p 48)))
    (h2 : OrientedPoseCovered continuousScout979Domain10_0 (p.square (ownerIndex p 16384)))
    : OrientedPoseCovered continuousScout979Domain6_21 (p.square (ownerIndex p 512)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout979Domain6_13 continuousScout979Domain6_21
    ![continuousScout979Domain2_2,continuousScout979Domain3_20,continuousScout979Domain10_0]
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
end N12Compact.Preservation.Chords.C979Step20

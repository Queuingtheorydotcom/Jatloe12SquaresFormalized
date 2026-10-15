import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C979

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C979Step17
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C979

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (167797199/100000000)
def hi : ℚ := (167925549/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (3986,radius64,radius64_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (8736,radius65,radius65_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (8737,radius66,radius66_checked,[.single 8, .single 2])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (8738,radius67,radius67_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (8739,radius68,radius68_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (8740,radius69,radius69_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (8741,radius70,radius70_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (8742,radius71,radius71_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (8743,radius72,radius72_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (8744,radius73,radius73_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (8745,radius74,radius74_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (8746,radius75,radius75_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (8747,radius76,radius76_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (8748,radius77,radius77_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (8749,radius78,radius78_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (8750,radius79,radius79_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (8751,radius80,radius80_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (8752,radius81,radius81_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (8753,radius82,radius82_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (8754,radius83,radius83_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (8755,radius84,radius84_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (8756,radius85,radius85_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (8757,radius86,radius86_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (8758,radius87,radius87_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (8759,radius88,radius88_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (8760,radius89,radius89_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (8761,radius90,radius90_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (8762,radius91,radius91_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (8763,radius92,radius92_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (8764,radius93,radius93_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (8765,radius94,radius94_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (8766,radius95,radius95_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (8767,radius96,radius96_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (8768,radius97,radius97_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (8769,radius159,radius159_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (8770,radius160,radius160_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (8771,radius161,radius161_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (8772,radius162,radius162_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (8773,radius163,radius163_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (8774,radius164,radius164_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (8775,radius165,radius165_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (8776,radius166,radius166_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (8777,radius167,radius167_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (8778,radius168,radius168_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (8779,radius169,radius169_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_45 (dictionary,horizontal,lo,hi) := (8780,radius170,radius170_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_46 (dictionary,horizontal,lo,hi) := (8781,radius171,radius171_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_47 (dictionary,horizontal,lo,hi) := (8782,radius172,radius172_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_48 (dictionary,horizontal,lo,hi) := (8783,radius173,radius173_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_49 (dictionary,horizontal,lo,hi) := (8784,radius174,radius174_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_50 (dictionary,horizontal,lo,hi) := (8785,radius175,radius175_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_51 (dictionary,horizontal,lo,hi) := (8786,radius176,radius176_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_52 (dictionary,horizontal,lo,hi) := (8787,radius177,radius177_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_53 (dictionary,horizontal,lo,hi) := (8788,radius178,radius178_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_54 (dictionary,horizontal,lo,hi) := (8789,radius179,radius179_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_55 (dictionary,horizontal,lo,hi) := (8790,radius180,radius180_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_56 (dictionary,horizontal,lo,hi) := (8791,radius181,radius181_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_57 (dictionary,horizontal,lo,hi) := (8792,radius182,radius182_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_58 (dictionary,horizontal,lo,hi) := (8793,radius183,radius183_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_59 (dictionary,horizontal,lo,hi) := (8794,radius184,radius184_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_60 (dictionary,horizontal,lo,hi) := (8795,radius185,radius185_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_61 (dictionary,horizontal,lo,hi) := (8796,radius186,radius186_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_62 (dictionary,horizontal,lo,hi) := (8797,radius187,radius187_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_63 (dictionary,horizontal,lo,hi) := (8798,radius188,radius188_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_64 (dictionary,horizontal,lo,hi) := (8799,radius189,radius189_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_65 (dictionary,horizontal,lo,hi) := (8800,radius190,radius190_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_66 (dictionary,horizontal,lo,hi) := (4098,radius191,radius191_checked,[.single 7, .single 2])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44, neighbor0_45, neighbor0_46, neighbor0_47,
    neighbor0_48, neighbor0_49, neighbor0_50, neighbor0_51, neighbor0_52, neighbor0_53, neighbor0_54, neighbor0_55, neighbor0_56, neighbor0_57, neighbor0_58, neighbor0_59,
    neighbor0_60, neighbor0_61, neighbor0_62, neighbor0_63, neighbor0_64, neighbor0_65, neighbor0_66]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout979Domain0_9Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (10628,radius64,radius64_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (10629,radius65,radius65_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (10630,radius66,radius66_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (10631,radius67,radius67_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (10632,radius68,radius68_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (10633,radius69,radius69_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (10634,radius70,radius70_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (10635,radius71,radius71_checked,[.single 10, .single 4])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (10636,radius72,radius72_checked,[.single 9, .single 4])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (10637,radius73,radius73_checked,[.single 9, .single 4])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (10638,radius74,radius74_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (10639,radius75,radius75_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (10640,radius76,radius76_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (10641,radius77,radius77_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (10642,radius78,radius78_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (10643,radius79,radius79_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (10644,radius80,radius80_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (10645,radius81,radius81_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (10646,radius82,radius82_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (10647,radius83,radius83_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (10648,radius84,radius84_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (10649,radius85,radius85_checked,[.single 9, .single 4])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (10650,radius86,radius86_checked,[.single 9, .single 4])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (10651,radius87,radius87_checked,[.single 9, .single 4])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (10652,radius88,radius88_checked,[.single 9, .single 4])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (10653,radius89,radius89_checked,[.single 9, .single 3])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (10654,radius90,radius90_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (10655,radius91,radius91_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (10656,radius92,radius92_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (10657,radius93,radius93_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (10658,radius94,radius94_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (10659,radius95,radius95_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (10660,radius96,radius96_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (10661,radius97,radius97_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (10662,radius98,radius98_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (10663,radius99,radius99_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (10664,radius100,radius100_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (10665,radius101,radius101_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (10666,radius102,radius102_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (10667,radius103,radius103_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (10668,radius104,radius104_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (10669,radius105,radius105_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (10670,radius106,radius106_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (10671,radius107,radius107_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (10672,radius108,radius108_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (10673,radius128,radius128_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (10674,radius129,radius129_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (10675,radius130,radius130_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (10676,radius131,radius131_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (10677,radius132,radius132_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (10678,radius133,radius133_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (10679,radius134,radius134_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (10680,radius135,radius135_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (10681,radius136,radius136_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (10682,radius137,radius137_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (10683,radius138,radius138_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (10684,radius139,radius139_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (10685,radius140,radius140_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (10686,radius141,radius141_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (10687,radius142,radius142_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (10688,radius143,radius143_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_61 (dictionary,horizontal,lo,hi) := (10689,radius144,radius144_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_62 (dictionary,horizontal,lo,hi) := (10690,radius145,radius145_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_63 (dictionary,horizontal,lo,hi) := (10691,radius146,radius146_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_64 (dictionary,horizontal,lo,hi) := (10692,radius147,radius147_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_65 (dictionary,horizontal,lo,hi) := (10693,radius148,radius148_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_66 (dictionary,horizontal,lo,hi) := (10694,radius149,radius149_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_67 (dictionary,horizontal,lo,hi) := (10695,radius150,radius150_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_68 (dictionary,horizontal,lo,hi) := (10696,radius151,radius151_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_69 (dictionary,horizontal,lo,hi) := (10697,radius152,radius152_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_70 (dictionary,horizontal,lo,hi) := (10698,radius153,radius153_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_71 (dictionary,horizontal,lo,hi) := (10699,radius154,radius154_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_72 (dictionary,horizontal,lo,hi) := (10700,radius155,radius155_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_73 (dictionary,horizontal,lo,hi) := (10701,radius156,radius156_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_74 (dictionary,horizontal,lo,hi) := (10702,radius157,radius157_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_75 (dictionary,horizontal,lo,hi) := (10703,radius158,radius158_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_76 (dictionary,horizontal,lo,hi) := (10704,radius159,radius159_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_77 (dictionary,horizontal,lo,hi) := (10705,radius160,radius160_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_78 (dictionary,horizontal,lo,hi) := (10706,radius161,radius161_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_79 (dictionary,horizontal,lo,hi) := (10707,radius162,radius162_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_80 (dictionary,horizontal,lo,hi) := (10708,radius163,radius163_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_81 (dictionary,horizontal,lo,hi) := (10709,radius164,radius164_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_82 (dictionary,horizontal,lo,hi) := (10710,radius165,radius165_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_83 (dictionary,horizontal,lo,hi) := (10711,radius166,radius166_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_84 (dictionary,horizontal,lo,hi) := (10712,radius167,radius167_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_85 (dictionary,horizontal,lo,hi) := (10713,radius168,radius168_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_86 (dictionary,horizontal,lo,hi) := (10714,radius169,radius169_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_87 (dictionary,horizontal,lo,hi) := (10715,radius170,radius170_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_88 (dictionary,horizontal,lo,hi) := (10716,radius171,radius171_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_89 (dictionary,horizontal,lo,hi) := (10717,radius172,radius172_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_90 (dictionary,horizontal,lo,hi) := (10718,radius173,radius173_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_91 (dictionary,horizontal,lo,hi) := (10719,radius174,radius174_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_92 (dictionary,horizontal,lo,hi) := (10720,radius175,radius175_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_93 (dictionary,horizontal,lo,hi) := (10721,radius176,radius176_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_94 (dictionary,horizontal,lo,hi) := (10722,radius177,radius177_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_95 (dictionary,horizontal,lo,hi) := (10723,radius178,radius178_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_96 (dictionary,horizontal,lo,hi) := (10724,radius179,radius179_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_97 (dictionary,horizontal,lo,hi) := (10725,radius180,radius180_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_98 (dictionary,horizontal,lo,hi) := (10726,radius181,radius181_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_99 (dictionary,horizontal,lo,hi) := (10727,radius182,radius182_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_100 (dictionary,horizontal,lo,hi) := (10728,radius183,radius183_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_101 (dictionary,horizontal,lo,hi) := (10729,radius184,radius184_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_102 (dictionary,horizontal,lo,hi) := (10730,radius185,radius185_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_103 (dictionary,horizontal,lo,hi) := (10731,radius186,radius186_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_104 (dictionary,horizontal,lo,hi) := (10732,radius187,radius187_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_105 (dictionary,horizontal,lo,hi) := (10733,radius188,radius188_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_106 (dictionary,horizontal,lo,hi) := (10734,radius189,radius189_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_107 (dictionary,horizontal,lo,hi) := (10735,radius190,radius190_checked,[.single 9, .single 5])
checked_chord_neighbor neighbor1_108 (dictionary,horizontal,lo,hi) := (10736,radius191,radius191_checked,[.single 10, .single 5])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53, neighbor1_54, neighbor1_55, neighbor1_56, neighbor1_57, neighbor1_58, neighbor1_59,
    neighbor1_60, neighbor1_61, neighbor1_62, neighbor1_63, neighbor1_64, neighbor1_65, neighbor1_66, neighbor1_67, neighbor1_68, neighbor1_69, neighbor1_70, neighbor1_71,
    neighbor1_72, neighbor1_73, neighbor1_74, neighbor1_75, neighbor1_76, neighbor1_77, neighbor1_78, neighbor1_79, neighbor1_80, neighbor1_81, neighbor1_82, neighbor1_83,
    neighbor1_84, neighbor1_85, neighbor1_86, neighbor1_87, neighbor1_88, neighbor1_89, neighbor1_90, neighbor1_91, neighbor1_92, neighbor1_93, neighbor1_94, neighbor1_95,
    neighbor1_96, neighbor1_97, neighbor1_98, neighbor1_99, neighbor1_100, neighbor1_101, neighbor1_102, neighbor1_103, neighbor1_104, neighbor1_105, neighbor1_106, neighbor1_107,
    neighbor1_108]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout979Domain5_10Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (11805,radius64,radius64_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (11806,radius65,radius65_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (11807,radius66,radius66_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (11808,radius67,radius67_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (11809,radius167,radius167_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (11810,radius168,radius168_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (11811,radius169,radius169_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (11812,radius170,radius170_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (11813,radius171,radius171_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (11814,radius172,radius172_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (11815,radius173,radius173_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (11816,radius174,radius174_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (11817,radius175,radius175_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (11818,radius176,radius176_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (11819,radius177,radius177_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (11820,radius178,radius178_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (11821,radius179,radius179_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (11822,radius180,radius180_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (11823,radius181,radius181_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (11824,radius182,radius182_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (11825,radius183,radius183_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (11826,radius184,radius184_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (11827,radius185,radius185_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (11828,radius186,radius186_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (11829,radius187,radius187_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (11830,radius188,radius188_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (11831,radius189,radius189_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (11832,radius190,radius190_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (11833,radius191,radius191_checked,[.single 7, .single 3])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27, neighbor2_28]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout979Domain7_16Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (9340,radius64,radius64_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9057,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (9341,radius65,radius65_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9058,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (9342,radius66,radius66_checked,chord_close%(⟨[0,10],[(20,0),(1,10)]⟩),chord_keep%(9059,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (9343,radius67,radius67_checked,chord_close%(⟨[0,10],[(16,0),(1,10)]⟩),chord_keep%(9060,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (9344,radius68,radius68_checked,chord_close%(⟨[0,10],[(4,0),(5,10)]⟩),chord_keep%(9061,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (9345,radius69,radius69_checked,chord_close%(⟨[0,9],[(1,0),(2,9)]⟩),chord_keep%(9062,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (9346,radius70,radius70_checked,chord_close%(⟨[0,10],[(1,0),(8,10)]⟩),chord_keep%(9063,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 5, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (9347,radius71,radius71_checked,chord_close%(⟨[0,9],[(16,0),(1,9)]⟩),chord_keep%(9064,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (9348,radius72,radius72_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9065,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (9349,radius73,radius73_checked,chord_close%(⟨[0,9],[(2,0),(1,9)]⟩),chord_keep%(9066,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (9350,radius74,radius74_checked,chord_close%(⟨[0,9],[(1,0),(8,9)]⟩),chord_keep%(9067,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (9351,radius75,radius75_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9068,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (9352,radius76,radius76_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9069,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (9353,radius77,radius77_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9070,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 14]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (9354,radius78,radius78_checked,chord_close%(⟨[0,9],[(1,0),(2,9)]⟩),chord_keep%(9071,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .single 3, .single 8, .copy 14]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (9355,radius79,radius79_checked,chord_close%(⟨[0,9],[(1,0),(4,9)]⟩),chord_keep%(9072,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 5, .single 3, .single 8, .copy 14]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (9356,radius80,radius80_checked,chord_close%(⟨[0,10],[(5,0),(4,10)]⟩),chord_keep%(9073,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (9357,radius81,radius81_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9074,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (9358,radius82,radius82_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9075,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (9359,radius83,radius83_checked,chord_close%(⟨[0,10],[(4,0),(1,10)]⟩),chord_keep%(9076,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (9360,radius84,radius84_checked,chord_close%(⟨[0,10],[(1,0),(8,10)]⟩),chord_keep%(9077,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (9361,radius85,radius85_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9078,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (9362,radius86,radius86_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9079,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (9363,radius87,radius87_checked,chord_close%(⟨[0,11],[(1,0),(5,11)]⟩),chord_keep%(9080,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 0, .single 0, .single 6, .single 3, .single 10, .copy 16]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (9364,radius88,radius88_checked,chord_close%(⟨[0,11],[(1,0),(1,11)]⟩),chord_keep%(9081,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 0, .single 0, .single 6, .single 3, .single 10, .copy 16]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (9365,radius89,radius89_checked,chord_close%(⟨[0,11],[(1,0),(1,11)]⟩),chord_keep%(9082,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 0, .single 0, .single 6, .single 3, .single 10, .copy 16]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (9366,radius90,radius90_checked,chord_close%(⟨[0,11],[(25,0),(1,11)]⟩),chord_keep%(9083,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 0, .single 0, .single 6, .single 3, .single 10, .copy 16]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (9367,radius91,radius91_checked,chord_close%(⟨[0,10],[(1,0),(5,10)]⟩),chord_keep%(9084,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (9368,radius92,radius92_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9085,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (9369,radius93,radius93_checked,chord_close%(⟨[0,10],[(1280,0),(1,10)]⟩),chord_keep%(9086,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (9370,radius94,radius94_checked,chord_close%(⟨[0,10],[(1,0),(4,10)]⟩),chord_keep%(9087,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (9371,radius95,radius95_checked,chord_close%(⟨[0,10],[(8,0),(1,10)]⟩),chord_keep%(9088,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (9372,radius96,radius96_checked,chord_close%(⟨[0,10],[(1,0),(10,10)]⟩),chord_keep%(9089,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (9373,radius97,radius97_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9090,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (9374,radius98,radius98_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9091,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (9375,radius99,radius99_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9092,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (9376,radius100,radius100_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9093,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 6, .single 3, .single 9, .copy 15]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (9377,radius101,radius101_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9094,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (9378,radius102,radius102_checked,chord_close%(⟨[0,10],[(32,0),(1,10)]⟩),chord_keep%(9095,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (9379,radius103,radius103_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9096,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (9380,radius104,radius104_checked,chord_close%(⟨[0,10],[(1,0),(4,10)]⟩),chord_keep%(9097,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (9381,radius105,radius105_checked,chord_close%(⟨[0,10],[(1,0),(4,10)]⟩),chord_keep%(9098,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (9382,radius106,radius106_checked,chord_close%(⟨[0,10],[(1,0),(32,10)]⟩),chord_keep%(9099,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (9383,radius107,radius107_checked,chord_close%(⟨[0,10],[(10,0),(1,10)]⟩),chord_keep%(9100,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (9384,radius108,radius108_checked,chord_close%(⟨[0,10],[(50,0),(1,10)]⟩),chord_keep%(9101,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (9385,radius109,radius109_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9102,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (9386,radius110,radius110_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9103,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (9387,radius111,radius111_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9104,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 3, .single 9, .copy 15]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (9388,radius112,radius112_checked,chord_close%(⟨[0,11],[(2,0),(1,11)]⟩),chord_keep%(9105,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 10, .single 0, .single 0, .single 8, .single 4, .single 10, .copy 16]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (9389,radius113,radius113_checked,chord_close%(⟨[0,10],[(40,0),(1,10)]⟩),chord_keep%(9106,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (9390,radius114,radius114_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9107,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (9391,radius115,radius115_checked,chord_close%(⟨[0,10],[(4,0),(1,10)]⟩),chord_keep%(9108,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (9392,radius116,radius116_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9109,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .pair 0 4, .single 9, .copy 15]))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (9393,radius117,radius117_checked,chord_close%(⟨[0,10],[(1,0),(16,10)]⟩),chord_keep%(9110,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (9394,radius118,radius118_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9111,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (9395,radius119,radius119_checked,chord_close%(⟨[0,10],[(2,0),(25,10)]⟩),chord_keep%(9112,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (9396,radius120,radius120_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9113,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (9397,radius121,radius121_checked,chord_close%(⟨[0,11],[(1,0),(4,11)]⟩),chord_keep%(9114,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 0, .single 0, .single 7, .single 4, .single 9, .copy 16]))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (9398,radius122,radius122_checked,chord_close%(⟨[0,10],[(1,0),(8,10)]⟩),chord_keep%(9115,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (9399,radius123,radius123_checked,chord_close%(⟨[0,10],[(1,0),(20,10)]⟩),chord_keep%(9116,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (9400,radius124,radius124_checked,chord_close%(⟨[0,10],[(2,0),(5,10)]⟩),chord_keep%(9117,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (9401,radius125,radius125_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9118,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (9402,radius126,radius126_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9119,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 6, .single 4, .single 8, .copy 15]))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (9403,radius127,radius127_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9120,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan64 (dictionary,horizontal,lo,hi) := (9404,radius128,radius128_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9121,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan65 (dictionary,horizontal,lo,hi) := (9405,radius129,radius129_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9122,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan66 (dictionary,horizontal,lo,hi) := (9406,radius130,radius130_checked,chord_close%(⟨[0,10],[(320,0),(1,10)]⟩),chord_keep%(9123,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan67 (dictionary,horizontal,lo,hi) := (9407,radius131,radius131_checked,chord_close%(⟨[0,10],[(8,0),(1,10)]⟩),chord_keep%(9124,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan68 (dictionary,horizontal,lo,hi) := (9408,radius132,radius132_checked,chord_close%(⟨[0,10],[(4,0),(5,10)]⟩),chord_keep%(9125,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan69 (dictionary,horizontal,lo,hi) := (9409,radius133,radius133_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9126,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan70 (dictionary,horizontal,lo,hi) := (9410,radius134,radius134_checked,chord_close%(⟨[0,10],[(25,0),(2,10)]⟩),chord_keep%(9127,[.pair 3 4, .single 4, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .single 4, .single 8, .copy 15]))
checked_chord_plan plan71 (dictionary,horizontal,lo,hi) := (9411,radius135,radius135_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9128,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan72 (dictionary,horizontal,lo,hi) := (9412,radius136,radius136_checked,chord_close%(⟨[0,10],[(5,0),(16,10)]⟩),chord_keep%(9129,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan73 (dictionary,horizontal,lo,hi) := (9413,radius137,radius137_checked,chord_close%(⟨[0,10],[(5,0),(2,10)]⟩),chord_keep%(9130,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan74 (dictionary,horizontal,lo,hi) := (9414,radius138,radius138_checked,chord_close%(⟨[0,10],[(8,0),(25,10)]⟩),chord_keep%(9131,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan75 (dictionary,horizontal,lo,hi) := (9415,radius139,radius139_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9132,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan76 (dictionary,horizontal,lo,hi) := (9416,radius140,radius140_checked,chord_close%(⟨[0,10],[(1,0),(16,10)]⟩),chord_keep%(9133,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan77 (dictionary,horizontal,lo,hi) := (9417,radius141,radius141_checked,chord_close%(⟨[0,10],[(1,0),(4,10)]⟩),chord_keep%(9134,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan78 (dictionary,horizontal,lo,hi) := (9418,radius142,radius142_checked,chord_close%(⟨[0,10],[(1,0),(10,10)]⟩),chord_keep%(9135,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan79 (dictionary,horizontal,lo,hi) := (9419,radius143,radius143_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9136,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan80 (dictionary,horizontal,lo,hi) := (9420,radius144,radius144_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9137,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan81 (dictionary,horizontal,lo,hi) := (9421,radius145,radius145_checked,chord_close%(⟨[0,10],[(1,0),(20,10)]⟩),chord_keep%(9138,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan82 (dictionary,horizontal,lo,hi) := (9422,radius146,radius146_checked,chord_close%(⟨[0,10],[(1,0),(4,10)]⟩),chord_keep%(9139,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan83 (dictionary,horizontal,lo,hi) := (9423,radius147,radius147_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9140,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan84 (dictionary,horizontal,lo,hi) := (9424,radius148,radius148_checked,chord_close%(⟨[0,11],[(1,0),(1,11)]⟩),chord_keep%(9141,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 16]))
checked_chord_plan plan85 (dictionary,horizontal,lo,hi) := (9425,radius149,radius149_checked,chord_close%(⟨[0,11],[(1,0),(25,11)]⟩),chord_keep%(9142,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 16]))
checked_chord_plan plan86 (dictionary,horizontal,lo,hi) := (9426,radius150,radius150_checked,chord_close%(⟨[0,10],[(1,0),(5,10)]⟩),chord_keep%(9143,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan87 (dictionary,horizontal,lo,hi) := (9427,radius151,radius151_checked,chord_close%(⟨[0,10],[(5,0),(4,10)]⟩),chord_keep%(9144,[.pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .single 3, .single 7, .copy 15]))
checked_chord_plan plan88 (dictionary,horizontal,lo,hi) := (9428,radius152,radius152_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9145,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan89 (dictionary,horizontal,lo,hi) := (9429,radius153,radius153_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_keep%(9146,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan90 (dictionary,horizontal,lo,hi) := (9430,radius154,radius154_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9147,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan91 (dictionary,horizontal,lo,hi) := (9431,radius155,radius155_checked,chord_close%(⟨[0,10],[(5,0),(4,10)]⟩),chord_keep%(9148,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan92 (dictionary,horizontal,lo,hi) := (9432,radius156,radius156_checked,chord_close%(⟨[0,10],[(1,0),(5,10)]⟩),chord_keep%(9149,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan93 (dictionary,horizontal,lo,hi) := (9433,radius157,radius157_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9150,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan94 (dictionary,horizontal,lo,hi) := (9434,radius158,radius158_checked,chord_close%(⟨[0,10],[(1,0),(4,10)]⟩),chord_keep%(9151,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan95 (dictionary,horizontal,lo,hi) := (9435,radius159,radius159_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9152,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan96 (dictionary,horizontal,lo,hi) := (9436,radius160,radius160_checked,chord_close%(⟨[0,10],[(1,0),(2,10)]⟩),chord_keep%(9153,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan97 (dictionary,horizontal,lo,hi) := (9437,radius161,radius161_checked,chord_close%(⟨[0,10],[(25,0),(1,10)]⟩),chord_keep%(9154,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan98 (dictionary,horizontal,lo,hi) := (9438,radius162,radius162_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9155,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan99 (dictionary,horizontal,lo,hi) := (9439,radius163,radius163_checked,chord_close%(⟨[0,9],[(2,0),(1,9)]⟩),chord_keep%(9156,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan100 (dictionary,horizontal,lo,hi) := (9440,radius164,radius164_checked,chord_close%(⟨[0,9],[(16,0),(1,9)]⟩),chord_keep%(9157,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan101 (dictionary,horizontal,lo,hi) := (9441,radius165,radius165_checked,chord_close%(⟨[0,9],[(1,0),(5,9)]⟩),chord_keep%(9158,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan102 (dictionary,horizontal,lo,hi) := (9442,radius166,radius166_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9159,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan103 (dictionary,horizontal,lo,hi) := (9443,radius167,radius167_checked,chord_close%(⟨[0,9],[(5,0),(4,9)]⟩),chord_keep%(9160,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan104 (dictionary,horizontal,lo,hi) := (9444,radius168,radius168_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9161,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan105 (dictionary,horizontal,lo,hi) := (9445,radius169,radius169_checked,chord_close%(⟨[0,9],[(1,0),(2,9)]⟩),chord_keep%(9162,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan106 (dictionary,horizontal,lo,hi) := (9446,radius170,radius170_checked,chord_close%(⟨[0,9],[(5,0),(2,9)]⟩),chord_keep%(9163,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan107 (dictionary,horizontal,lo,hi) := (9447,radius171,radius171_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9164,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan108 (dictionary,horizontal,lo,hi) := (9448,radius172,radius172_checked,chord_close%(⟨[0,9],[(1,0),(2,9)]⟩),chord_keep%(9165,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan109 (dictionary,horizontal,lo,hi) := (9449,radius173,radius173_checked,chord_close%(⟨[0,9],[(1,0),(4,9)]⟩),chord_keep%(9166,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan110 (dictionary,horizontal,lo,hi) := (9450,radius174,radius174_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9167,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan111 (dictionary,horizontal,lo,hi) := (9451,radius175,radius175_checked,chord_close%(⟨[0,9],[(2,0),(5,9)]⟩),chord_keep%(9168,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan112 (dictionary,horizontal,lo,hi) := (9452,radius176,radius176_checked,chord_close%(⟨[0,9],[(2,0),(5,9)]⟩),chord_keep%(9169,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan113 (dictionary,horizontal,lo,hi) := (9453,radius177,radius177_checked,chord_close%(⟨[0,9],[(40,0),(1,9)]⟩),chord_keep%(9170,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan114 (dictionary,horizontal,lo,hi) := (9454,radius178,radius178_checked,chord_close%(⟨[0,9],[(1,0),(2,9)]⟩),chord_keep%(9171,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan115 (dictionary,horizontal,lo,hi) := (9455,radius179,radius179_checked,chord_close%(⟨[0,9],[(4,0),(1,9)]⟩),chord_keep%(9172,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan116 (dictionary,horizontal,lo,hi) := (9456,radius180,radius180_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9173,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan117 (dictionary,horizontal,lo,hi) := (9457,radius181,radius181_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(9174,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan118 (dictionary,horizontal,lo,hi) := (9458,radius182,radius182_checked,chord_close%(⟨[0,9],[(2,0),(1,9)]⟩),chord_keep%(9175,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 0, .single 0, .single 5, .pair 0 3, .single 6, .copy 14]))
checked_chord_plan plan119 (dictionary,horizontal,lo,hi) := (9459,radius183,radius183_checked,chord_close%(⟨[0,10],[(5,0),(1,10)]⟩),chord_keep%(9176,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan120 (dictionary,horizontal,lo,hi) := (9460,radius184,radius184_checked,chord_close%(⟨[0,10],[(4,0),(5,10)]⟩),chord_keep%(9177,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan121 (dictionary,horizontal,lo,hi) := (9461,radius185,radius185_checked,chord_close%(⟨[0,10],[(160,0),(1,10)]⟩),chord_keep%(9178,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan122 (dictionary,horizontal,lo,hi) := (9462,radius186,radius186_checked,chord_close%(⟨[0,10],[(1,0),(5,10)]⟩),chord_keep%(9179,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan123 (dictionary,horizontal,lo,hi) := (9463,radius187,radius187_checked,chord_close%(⟨[0,10],[(1,0),(8,10)]⟩),chord_keep%(9180,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan124 (dictionary,horizontal,lo,hi) := (9464,radius188,radius188_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_keep%(9181,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan125 (dictionary,horizontal,lo,hi) := (9465,radius189,radius189_checked,chord_close%(⟨[0,11],[(5,0),(1,11)]⟩),chord_keep%(9182,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .single 0, .single 0, .single 7, .pair 0 4, .single 8, .copy 16]))
checked_chord_plan plan126 (dictionary,horizontal,lo,hi) := (9466,radius190,radius190_checked,chord_close%(⟨[0,10],[(1,0),(32,10)]⟩),chord_keep%(9183,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
checked_chord_plan plan127 (dictionary,horizontal,lo,hi) := (9467,radius191,radius191_checked,chord_close%(⟨[0,10],[(16,0),(1,10)]⟩),chord_keep%(9184,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 0, .single 0, .single 6, .pair 0 4, .single 7, .copy 15]))
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
    plan120, plan121, plan122, plan123, plan124, plan125, plan126, plan127]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout979Domain11_7Ids := by rfl
def outputIds : List (Fin poseCount) := [9057,9058,9059,9060,9061,9062,9063,9064,9065,9066,9067,9068,9069,9070,9071,9072,9073,9074,9075,9076,9077,9078,9079,9080,9081,9082,9083,9084,9085,9086,9087,9088,9089,9090,9091,9092,9093,9094,9095,9096,9097,9098,9099,9100,9101,9102,9103,9104,9105,9106,9107,9108,9109,9110,9111,9112,9113,9114,9115,9116,9117,9118,9119,9120,9121,9122,9123,9124,9125,9126,9127,9128,9129,9130,9131,9132,9133,9134,9135,9136,9137,9138,9139,9140,9141,9142,9143,9144,9145,9146,9147,9148,9149,9150,9151,9152,9153,9154,9155,9156,9157,9158,9159,9160,9161,9162,9163,9164,9165,9166,9167,9168,9169,9170,9171,9172,9173,9174,9175,9176,9177,9178,9179,9180,9181,9182,9183,9184]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout979Domain11_18Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout979Domain11_18Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout979Domain11_7 (q 0))
    (h0 : OrientedPoseCovered continuousScout979Domain0_9 (q 1))
    (h1 : OrientedPoseCovered continuousScout979Domain5_10 (q 2))
    (h2 : OrientedPoseCovered continuousScout979Domain7_16 (q 3))
    : OrientedPoseCovered continuousScout979Domain11_18 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout979Domain11_7Ids continuousScout979Domain11_18Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain0_9Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain5_10Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain7_16Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![32768,1,256,3072]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout979Domain11_7 (p.square (ownerIndex p 32768)))
    (h0 : OrientedPoseCovered continuousScout979Domain0_9 (p.square (ownerIndex p 1)))
    (h1 : OrientedPoseCovered continuousScout979Domain5_10 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout979Domain7_16 (p.square (ownerIndex p 3072)))
    : OrientedPoseCovered continuousScout979Domain11_18 (p.square (ownerIndex p 32768)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout979Domain11_7 continuousScout979Domain11_18
    ![continuousScout979Domain0_9,continuousScout979Domain5_10,continuousScout979Domain7_16]
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
end N12Compact.Preservation.Chords.C979Step17

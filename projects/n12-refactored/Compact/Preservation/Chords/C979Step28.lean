import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C979

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C979Step28
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C979

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (159794611/100000000)
def hi : ℚ := (45499829/25000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (8621,radius64,radius64_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (8622,radius65,radius65_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (8623,radius66,radius66_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (8624,radius191,radius191_checked,[.single 6, .single 2])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout979Domain0_27Ids := by rfl

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

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (11834,radius64,radius64_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (11835,radius65,radius65_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (11836,radius66,radius66_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (11837,radius167,radius167_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (11838,radius168,radius168_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (11839,radius169,radius169_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (11840,radius170,radius170_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (11841,radius171,radius171_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (11842,radius172,radius172_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (11843,radius173,radius173_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (11844,radius174,radius174_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (11845,radius175,radius175_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (11846,radius176,radius176_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (11847,radius177,radius177_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (11848,radius178,radius178_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (11849,radius179,radius179_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (11850,radius180,radius180_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (11851,radius181,radius181_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (11852,radius182,radius182_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (11853,radius183,radius183_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (11854,radius184,radius184_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (11855,radius185,radius185_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (11856,radius186,radius186_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (11857,radius187,radius187_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (11858,radius188,radius188_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (11859,radius189,radius189_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (11860,radius190,radius190_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (11861,radius191,radius191_checked,[.single 6, .single 2])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26, neighbor2_27]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout979Domain7_25Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (10212,radius64,radius64_checked,chord_close%(⟨[0,6],[(2,0),(1,6)]⟩),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (10213,radius65,radius65_checked,chord_close%(⟨[0,6],[(1,0),(40,6)]⟩),chord_close%(⟨[0,3],[(1,0),(4,3)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (10214,radius66,radius66_checked,chord_close%(⟨[0,6],[(16,0),(1,6)]⟩),chord_close%(⟨[0,3],[(5,0),(4,3)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (10215,radius67,radius67_checked,chord_close%(⟨[0,6],[(20,0),(1,6)]⟩),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (10216,radius68,radius68_checked,chord_close%(⟨[0,6],[(8,0),(1,6)]⟩),chord_close%(⟨[0,3],[(1,0),(10,3)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (10217,radius69,radius69_checked,chord_close%(⟨[0,6],[(1,0),(8,6)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (10218,radius70,radius70_checked,chord_close%(⟨[0,6],[(1,0),(50,6)]⟩),chord_close%(⟨[0,3],[(4,0),(5,3)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (10219,radius71,radius71_checked,chord_close%(⟨[0,6],[(62500,0),(1,6)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (10220,radius72,radius72_checked,chord_close%(⟨[0,6],[(1,0),(10,6)]⟩),chord_close%(⟨[0,3],[(64,0),(1,3)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (10221,radius73,radius73_checked,chord_close%(⟨[0,6],[(2,0),(5,6)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (10222,radius74,radius74_checked,chord_close%(⟨[0,6],[(1,0),(2,6)]⟩),chord_close%(⟨[0,3],[(8,0),(1,3)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (10223,radius93,radius93_checked,chord_keep%(10322,[.pair 1 5, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 6, .single 0, .pair 0 1, .single 5, .copy 11]),chord_close%(⟨[0,3],[(5,0),(2,3)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (10224,radius94,radius94_checked,chord_keep%(10323,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (10225,radius95,radius95_checked,chord_keep%(10324,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (10226,radius96,radius96_checked,chord_keep%(10325,[.pair 1 7, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .pair 0 1, .single 7, .copy 13]),chord_close%(⟨[0,4],[(8,0),(1,4)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (10227,radius97,radius97_checked,chord_keep%(10326,[.pair 1 7, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .pair 0 1, .single 7, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (10228,radius98,radius98_checked,chord_keep%(10327,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (10229,radius99,radius99_checked,chord_keep%(10328,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (10230,radius100,radius100_checked,chord_keep%(10329,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (10231,radius101,radius101_checked,chord_keep%(10330,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (10232,radius102,radius102_checked,chord_keep%(10331,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (10233,radius103,radius103_checked,chord_keep%(10332,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (10234,radius104,radius104_checked,chord_keep%(10333,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (10235,radius105,radius105_checked,chord_keep%(10334,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (10236,radius106,radius106_checked,chord_keep%(10335,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(8,3)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (10237,radius107,radius107_checked,chord_keep%(10336,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(5,0),(4,3)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (10238,radius108,radius108_checked,chord_keep%(10337,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(5,0),(8,3)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (10239,radius109,radius109_checked,chord_keep%(10338,[.pair 1 6, .pair 0 1, .single 0, .pair 4 5, .single 5, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (10240,radius110,radius110_checked,chord_keep%(10339,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (10241,radius111,radius111_checked,chord_keep%(10340,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (10242,radius112,radius112_checked,chord_keep%(10341,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (10243,radius113,radius113_checked,chord_keep%(10342,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(25,0),(1,3)]⟩))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (10244,radius114,radius114_checked,chord_keep%(10343,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (10245,radius115,radius115_checked,chord_keep%(10344,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(50,3)]⟩))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (10246,radius116,radius116_checked,chord_keep%(10345,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (10247,radius117,radius117_checked,chord_keep%(10346,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (10248,radius118,radius118_checked,chord_keep%(10347,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(4,3)]⟩))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (10249,radius119,radius119_checked,chord_keep%(10348,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (10250,radius120,radius120_checked,chord_keep%(10349,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (10251,radius121,radius121_checked,chord_keep%(10350,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (10252,radius122,radius122_checked,chord_keep%(10351,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(1,0),(4,3)]⟩))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (10253,radius123,radius123_checked,chord_keep%(10352,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,3],[(2,0),(1,3)]⟩))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (10254,radius124,radius124_checked,chord_keep%(10353,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(32,4)]⟩))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (10255,radius125,radius125_checked,chord_keep%(10354,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (10256,radius126,radius126_checked,chord_keep%(10355,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(5,0),(8,4)]⟩))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (10257,radius127,radius127_checked,chord_keep%(10356,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (10258,radius128,radius128_checked,chord_keep%(10357,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(4,0),(1,4)]⟩))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (10259,radius129,radius129_checked,chord_keep%(10358,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(50,0),(1,4)]⟩))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (10260,radius130,radius130_checked,chord_keep%(10359,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(125,0),(1,4)]⟩))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (10261,radius131,radius131_checked,chord_keep%(10360,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (10262,radius132,radius132_checked,chord_keep%(10361,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (10263,radius133,radius133_checked,chord_keep%(10362,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(4,0),(25,4)]⟩))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (10264,radius134,radius134_checked,chord_keep%(10363,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(5,0),(16,4)]⟩))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (10265,radius135,radius135_checked,chord_keep%(10364,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (10266,radius136,radius136_checked,chord_keep%(10365,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (10267,radius137,radius137_checked,chord_keep%(10366,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (10268,radius138,radius138_checked,chord_keep%(10367,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (10269,radius139,radius139_checked,chord_keep%(10368,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (10270,radius140,radius140_checked,chord_keep%(10369,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (10271,radius141,radius141_checked,chord_keep%(10370,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(4,0),(1,4)]⟩))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (10272,radius142,radius142_checked,chord_keep%(10371,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(10,4)]⟩))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (10273,radius143,radius143_checked,chord_keep%(10372,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (10274,radius144,radius144_checked,chord_keep%(10373,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (10275,radius145,radius145_checked,chord_keep%(10374,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan64 (dictionary,horizontal,lo,hi) := (10276,radius146,radius146_checked,chord_keep%(10375,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(8,0),(5,4)]⟩))
checked_chord_plan plan65 (dictionary,horizontal,lo,hi) := (10277,radius147,radius147_checked,chord_keep%(10376,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan66 (dictionary,horizontal,lo,hi) := (10278,radius148,radius148_checked,chord_keep%(10377,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(20,4)]⟩))
checked_chord_plan plan67 (dictionary,horizontal,lo,hi) := (10279,radius149,radius149_checked,chord_keep%(10378,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan68 (dictionary,horizontal,lo,hi) := (10280,radius150,radius150_checked,chord_keep%(10379,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(16,0),(1,4)]⟩))
checked_chord_plan plan69 (dictionary,horizontal,lo,hi) := (10281,radius151,radius151_checked,chord_keep%(10380,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan70 (dictionary,horizontal,lo,hi) := (10282,radius152,radius152_checked,chord_keep%(10381,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(80,0),(1,4)]⟩))
checked_chord_plan plan71 (dictionary,horizontal,lo,hi) := (10283,radius153,radius153_checked,chord_keep%(10382,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(125,4)]⟩))
checked_chord_plan plan72 (dictionary,horizontal,lo,hi) := (10284,radius154,radius154_checked,chord_keep%(10383,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan73 (dictionary,horizontal,lo,hi) := (10285,radius155,radius155_checked,chord_keep%(10384,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1280,0),(1,4)]⟩))
checked_chord_plan plan74 (dictionary,horizontal,lo,hi) := (10286,radius156,radius156_checked,chord_keep%(10385,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(16,0),(1,4)]⟩))
checked_chord_plan plan75 (dictionary,horizontal,lo,hi) := (10287,radius157,radius157_checked,chord_keep%(10386,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(4,0),(1,4)]⟩))
checked_chord_plan plan76 (dictionary,horizontal,lo,hi) := (10288,radius158,radius158_checked,chord_keep%(10387,[.pair 1 6, .pair 0 1, .single 0, .single 6, .single 7, .single 7, .single 0, .pair 0 1, .single 6, .copy 12]),chord_close%(⟨[0,4],[(1,0),(32,4)]⟩))
checked_chord_plan plan77 (dictionary,horizontal,lo,hi) := (10289,radius159,radius159_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan78 (dictionary,horizontal,lo,hi) := (10290,radius160,radius160_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan79 (dictionary,horizontal,lo,hi) := (10291,radius161,radius161_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_close%(⟨[0,4],[(8,0),(125,4)]⟩))
checked_chord_plan plan80 (dictionary,horizontal,lo,hi) := (10292,radius162,radius162_checked,chord_close%(⟨[0,7],[(5,0),(8,7)]⟩),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan81 (dictionary,horizontal,lo,hi) := (10293,radius163,radius163_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan82 (dictionary,horizontal,lo,hi) := (10294,radius164,radius164_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan83 (dictionary,horizontal,lo,hi) := (10295,radius165,radius165_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_close%(⟨[0,4],[(1,0),(25,4)]⟩))
checked_chord_plan plan84 (dictionary,horizontal,lo,hi) := (10296,radius166,radius166_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan85 (dictionary,horizontal,lo,hi) := (10297,radius167,radius167_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_close%(⟨[0,4],[(40,0),(1,4)]⟩))
checked_chord_plan plan86 (dictionary,horizontal,lo,hi) := (10298,radius168,radius168_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan87 (dictionary,horizontal,lo,hi) := (10299,radius169,radius169_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan88 (dictionary,horizontal,lo,hi) := (10300,radius170,radius170_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan89 (dictionary,horizontal,lo,hi) := (10301,radius171,radius171_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_close%(⟨[0,4],[(25,0),(1,4)]⟩))
checked_chord_plan plan90 (dictionary,horizontal,lo,hi) := (10302,radius172,radius172_checked,chord_close%(⟨[0,7],[(1,0),(16,7)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan91 (dictionary,horizontal,lo,hi) := (10303,radius173,radius173_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan92 (dictionary,horizontal,lo,hi) := (10304,radius174,radius174_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan93 (dictionary,horizontal,lo,hi) := (10305,radius175,radius175_checked,chord_close%(⟨[0,7],[(4,0),(5,7)]⟩),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan94 (dictionary,horizontal,lo,hi) := (10306,radius176,radius176_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan95 (dictionary,horizontal,lo,hi) := (10307,radius177,radius177_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_close%(⟨[0,4],[(25,0),(1,4)]⟩))
checked_chord_plan plan96 (dictionary,horizontal,lo,hi) := (10308,radius178,radius178_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan97 (dictionary,horizontal,lo,hi) := (10309,radius179,radius179_checked,chord_close%(⟨[0,7],[(4,0),(25,7)]⟩),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan98 (dictionary,horizontal,lo,hi) := (10310,radius180,radius180_checked,chord_close%(⟨[0,7],[(1,0),(20,7)]⟩),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan99 (dictionary,horizontal,lo,hi) := (10311,radius181,radius181_checked,chord_close%(⟨[0,7],[(5,0),(2,7)]⟩),chord_close%(⟨[0,4],[(4,0),(1,4)]⟩))
checked_chord_plan plan100 (dictionary,horizontal,lo,hi) := (10312,radius182,radius182_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan101 (dictionary,horizontal,lo,hi) := (10313,radius183,radius183_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_close%(⟨[0,4],[(10,0),(1,4)]⟩))
checked_chord_plan plan102 (dictionary,horizontal,lo,hi) := (10314,radius184,radius184_checked,chord_close%(⟨[0,7],[(32,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan103 (dictionary,horizontal,lo,hi) := (10315,radius185,radius185_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan104 (dictionary,horizontal,lo,hi) := (10316,radius186,radius186_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan105 (dictionary,horizontal,lo,hi) := (10317,radius187,radius187_checked,chord_close%(⟨[0,7],[(40,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan106 (dictionary,horizontal,lo,hi) := (10318,radius188,radius188_checked,chord_close%(⟨[0,6],[(1,0),(50,6)]⟩),chord_close%(⟨[0,4],[(8,0),(1,4)]⟩))
checked_chord_plan plan107 (dictionary,horizontal,lo,hi) := (10319,radius189,radius189_checked,chord_close%(⟨[0,6],[(1,0),(2,6)]⟩),chord_close%(⟨[0,4],[(32,0),(1,4)]⟩))
checked_chord_plan plan108 (dictionary,horizontal,lo,hi) := (10320,radius190,radius190_checked,chord_close%(⟨[0,6],[(1,0),(4,6)]⟩),chord_close%(⟨[0,4],[(2,0),(5,4)]⟩))
checked_chord_plan plan109 (dictionary,horizontal,lo,hi) := (10321,radius191,radius191_checked,chord_close%(⟨[0,6],[(4,0),(1,6)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
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
    plan108, plan109]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout979Domain4_28Ids := by rfl
def outputIds : List (Fin poseCount) := [10322,10323,10324,10325,10326,10327,10328,10329,10330,10331,10332,10333,10334,10335,10336,10337,10338,10339,10340,10341,10342,10343,10344,10345,10346,10347,10348,10349,10350,10351,10352,10353,10354,10355,10356,10357,10358,10359,10360,10361,10362,10363,10364,10365,10366,10367,10368,10369,10370,10371,10372,10373,10374,10375,10376,10377,10378,10379,10380,10381,10382,10383,10384,10385,10386,10387]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout979Domain4_29Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout979Domain4_29Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout979Domain4_28 (q 0))
    (h0 : OrientedPoseCovered continuousScout979Domain0_27 (q 1))
    (h1 : OrientedPoseCovered continuousScout979Domain5_10 (q 2))
    (h2 : OrientedPoseCovered continuousScout979Domain7_25 (q 3))
    : OrientedPoseCovered continuousScout979Domain4_29 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout979Domain4_28Ids continuousScout979Domain4_29Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain0_27Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain5_10Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain7_25Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![192,1,256,3072]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout979Domain4_28 (p.square (ownerIndex p 192)))
    (h0 : OrientedPoseCovered continuousScout979Domain0_27 (p.square (ownerIndex p 1)))
    (h1 : OrientedPoseCovered continuousScout979Domain5_10 (p.square (ownerIndex p 256)))
    (h2 : OrientedPoseCovered continuousScout979Domain7_25 (p.square (ownerIndex p 3072)))
    : OrientedPoseCovered continuousScout979Domain4_29 (p.square (ownerIndex p 192)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout979Domain4_28 continuousScout979Domain4_29
    ![continuousScout979Domain0_27,continuousScout979Domain5_10,continuousScout979Domain7_25]
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
end N12Compact.Preservation.Chords.C979Step28

import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C979

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C979Step27
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C979

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (45421717/50000000)
def hi : ℚ := (45703571/50000000)
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

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (2550,radius64,radius64_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (4151,radius65,radius65_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (4152,radius66,radius66_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (4153,radius67,radius67_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (4154,radius68,radius68_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (4155,radius69,radius69_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (4156,radius70,radius70_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (4157,radius71,radius71_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (4158,radius72,radius72_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (4159,radius73,radius73_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (4160,radius74,radius74_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (4161,radius75,radius75_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (4162,radius76,radius76_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (4163,radius77,radius77_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (4164,radius78,radius78_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (4165,radius79,radius79_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (4166,radius80,radius80_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (4167,radius81,radius81_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (4168,radius82,radius82_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (4169,radius83,radius83_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (4170,radius84,radius84_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (4171,radius85,radius85_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (4172,radius86,radius86_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (4173,radius87,radius87_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (4174,radius88,radius88_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (4175,radius89,radius89_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (4176,radius90,radius90_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (4177,radius91,radius91_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (4178,radius92,radius92_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (4179,radius93,radius93_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (4180,radius94,radius94_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (4181,radius95,radius95_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (4182,radius96,radius96_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (4183,radius97,radius97_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (4184,radius98,radius98_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (4185,radius99,radius99_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (4186,radius100,radius100_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (4187,radius101,radius101_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (4188,radius102,radius102_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (4189,radius103,radius103_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (4190,radius104,radius104_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (4191,radius105,radius105_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (4192,radius106,radius106_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (4193,radius107,radius107_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (4194,radius108,radius108_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (4195,radius109,radius109_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (4196,radius110,radius110_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (4197,radius111,radius111_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (4198,radius112,radius112_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (4199,radius113,radius113_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (4200,radius114,radius114_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (4201,radius115,radius115_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (4202,radius116,radius116_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (4203,radius117,radius117_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (4204,radius118,radius118_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (4205,radius119,radius119_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (4206,radius120,radius120_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (4207,radius121,radius121_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (4208,radius122,radius122_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (4209,radius123,radius123_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (4210,radius124,radius124_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_61 (dictionary,horizontal,lo,hi) := (4211,radius125,radius125_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_62 (dictionary,horizontal,lo,hi) := (4212,radius126,radius126_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_63 (dictionary,horizontal,lo,hi) := (4213,radius127,radius127_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_64 (dictionary,horizontal,lo,hi) := (4214,radius128,radius128_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_65 (dictionary,horizontal,lo,hi) := (4215,radius129,radius129_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_66 (dictionary,horizontal,lo,hi) := (9468,radius130,radius130_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_67 (dictionary,horizontal,lo,hi) := (9469,radius131,radius131_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_68 (dictionary,horizontal,lo,hi) := (9470,radius132,radius132_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_69 (dictionary,horizontal,lo,hi) := (9471,radius133,radius133_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_70 (dictionary,horizontal,lo,hi) := (9472,radius134,radius134_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_71 (dictionary,horizontal,lo,hi) := (9473,radius135,radius135_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_72 (dictionary,horizontal,lo,hi) := (9474,radius136,radius136_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_73 (dictionary,horizontal,lo,hi) := (9475,radius137,radius137_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_74 (dictionary,horizontal,lo,hi) := (9476,radius138,radius138_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_75 (dictionary,horizontal,lo,hi) := (4225,radius139,radius139_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_76 (dictionary,horizontal,lo,hi) := (4226,radius140,radius140_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_77 (dictionary,horizontal,lo,hi) := (4227,radius141,radius141_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_78 (dictionary,horizontal,lo,hi) := (4228,radius142,radius142_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_79 (dictionary,horizontal,lo,hi) := (4229,radius143,radius143_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_80 (dictionary,horizontal,lo,hi) := (4230,radius144,radius144_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_81 (dictionary,horizontal,lo,hi) := (4231,radius145,radius145_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_82 (dictionary,horizontal,lo,hi) := (4232,radius146,radius146_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_83 (dictionary,horizontal,lo,hi) := (4233,radius147,radius147_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_84 (dictionary,horizontal,lo,hi) := (4234,radius148,radius148_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_85 (dictionary,horizontal,lo,hi) := (4235,radius149,radius149_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_86 (dictionary,horizontal,lo,hi) := (4236,radius150,radius150_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_87 (dictionary,horizontal,lo,hi) := (4237,radius151,radius151_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_88 (dictionary,horizontal,lo,hi) := (4238,radius152,radius152_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_89 (dictionary,horizontal,lo,hi) := (4239,radius153,radius153_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_90 (dictionary,horizontal,lo,hi) := (4240,radius154,radius154_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_91 (dictionary,horizontal,lo,hi) := (4241,radius155,radius155_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_92 (dictionary,horizontal,lo,hi) := (4242,radius156,radius156_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_93 (dictionary,horizontal,lo,hi) := (4243,radius157,radius157_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_94 (dictionary,horizontal,lo,hi) := (4244,radius158,radius158_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_95 (dictionary,horizontal,lo,hi) := (4245,radius159,radius159_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_96 (dictionary,horizontal,lo,hi) := (4246,radius160,radius160_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_97 (dictionary,horizontal,lo,hi) := (4247,radius161,radius161_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_98 (dictionary,horizontal,lo,hi) := (4248,radius162,radius162_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_99 (dictionary,horizontal,lo,hi) := (4249,radius163,radius163_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_100 (dictionary,horizontal,lo,hi) := (4250,radius164,radius164_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_101 (dictionary,horizontal,lo,hi) := (4251,radius165,radius165_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_102 (dictionary,horizontal,lo,hi) := (4252,radius166,radius166_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_103 (dictionary,horizontal,lo,hi) := (4253,radius167,radius167_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_104 (dictionary,horizontal,lo,hi) := (4254,radius168,radius168_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_105 (dictionary,horizontal,lo,hi) := (4255,radius169,radius169_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_106 (dictionary,horizontal,lo,hi) := (4256,radius170,radius170_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_107 (dictionary,horizontal,lo,hi) := (4257,radius171,radius171_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_108 (dictionary,horizontal,lo,hi) := (4258,radius172,radius172_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_109 (dictionary,horizontal,lo,hi) := (4259,radius173,radius173_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_110 (dictionary,horizontal,lo,hi) := (4260,radius174,radius174_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_111 (dictionary,horizontal,lo,hi) := (4261,radius175,radius175_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_112 (dictionary,horizontal,lo,hi) := (4262,radius176,radius176_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_113 (dictionary,horizontal,lo,hi) := (4263,radius177,radius177_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_114 (dictionary,horizontal,lo,hi) := (4264,radius178,radius178_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_115 (dictionary,horizontal,lo,hi) := (4265,radius179,radius179_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_116 (dictionary,horizontal,lo,hi) := (4266,radius180,radius180_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_117 (dictionary,horizontal,lo,hi) := (4267,radius181,radius181_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_118 (dictionary,horizontal,lo,hi) := (4268,radius182,radius182_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_119 (dictionary,horizontal,lo,hi) := (4269,radius183,radius183_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_120 (dictionary,horizontal,lo,hi) := (4270,radius184,radius184_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_121 (dictionary,horizontal,lo,hi) := (4271,radius185,radius185_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_122 (dictionary,horizontal,lo,hi) := (4272,radius186,radius186_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_123 (dictionary,horizontal,lo,hi) := (4273,radius187,radius187_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_124 (dictionary,horizontal,lo,hi) := (4274,radius188,radius188_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_125 (dictionary,horizontal,lo,hi) := (4275,radius189,radius189_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_126 (dictionary,horizontal,lo,hi) := (4276,radius190,radius190_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor1_127 (dictionary,horizontal,lo,hi) := (2669,radius191,radius191_checked,[.single 7, .single 4])
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
    neighbor1_108, neighbor1_109, neighbor1_110, neighbor1_111, neighbor1_112, neighbor1_113, neighbor1_114, neighbor1_115, neighbor1_116, neighbor1_117, neighbor1_118, neighbor1_119,
    neighbor1_120, neighbor1_121, neighbor1_122, neighbor1_123, neighbor1_124, neighbor1_125, neighbor1_126, neighbor1_127]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout979Domain1_1Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (11956,radius64,radius64_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (11957,radius65,radius65_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (11958,radius66,radius66_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (11959,radius67,radius67_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (11960,radius68,radius68_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (3534,radius69,radius69_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (3535,radius70,radius70_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (3536,radius71,radius71_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (3537,radius72,radius72_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (3538,radius73,radius73_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (3539,radius74,radius74_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (3540,radius75,radius75_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (3541,radius76,radius76_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (3542,radius77,radius77_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (3543,radius78,radius78_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (3544,radius79,radius79_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (3545,radius80,radius80_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (3546,radius81,radius81_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (3547,radius82,radius82_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (3548,radius83,radius83_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (3549,radius84,radius84_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (3550,radius85,radius85_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (3551,radius86,radius86_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (3552,radius87,radius87_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (3553,radius88,radius88_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (3554,radius89,radius89_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (3555,radius90,radius90_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (3556,radius91,radius91_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (3557,radius92,radius92_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (3558,radius93,radius93_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (3559,radius94,radius94_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (3560,radius95,radius95_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (3561,radius96,radius96_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (3562,radius97,radius97_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (3563,radius98,radius98_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (3564,radius99,radius99_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (3565,radius100,radius100_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (3566,radius101,radius101_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (3567,radius102,radius102_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (3568,radius103,radius103_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (3569,radius104,radius104_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (3570,radius105,radius105_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (3571,radius106,radius106_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (3572,radius107,radius107_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (3573,radius108,radius108_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (3574,radius109,radius109_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (3575,radius110,radius110_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (3576,radius111,radius111_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (3577,radius112,radius112_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (3578,radius128,radius128_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (3579,radius129,radius129_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (3580,radius130,radius130_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_52 (dictionary,horizontal,lo,hi) := (3581,radius131,radius131_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_53 (dictionary,horizontal,lo,hi) := (3582,radius132,radius132_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_54 (dictionary,horizontal,lo,hi) := (3583,radius133,radius133_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_55 (dictionary,horizontal,lo,hi) := (3584,radius134,radius134_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_56 (dictionary,horizontal,lo,hi) := (3585,radius135,radius135_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_57 (dictionary,horizontal,lo,hi) := (3586,radius136,radius136_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_58 (dictionary,horizontal,lo,hi) := (3587,radius137,radius137_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_59 (dictionary,horizontal,lo,hi) := (3588,radius138,radius138_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_60 (dictionary,horizontal,lo,hi) := (3589,radius139,radius139_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_61 (dictionary,horizontal,lo,hi) := (3590,radius140,radius140_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_62 (dictionary,horizontal,lo,hi) := (3591,radius141,radius141_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_63 (dictionary,horizontal,lo,hi) := (3592,radius142,radius142_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_64 (dictionary,horizontal,lo,hi) := (3593,radius143,radius143_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_65 (dictionary,horizontal,lo,hi) := (3594,radius144,radius144_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_66 (dictionary,horizontal,lo,hi) := (3595,radius145,radius145_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_67 (dictionary,horizontal,lo,hi) := (3596,radius146,radius146_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_68 (dictionary,horizontal,lo,hi) := (3597,radius147,radius147_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_69 (dictionary,horizontal,lo,hi) := (3598,radius148,radius148_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_70 (dictionary,horizontal,lo,hi) := (3599,radius149,radius149_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_71 (dictionary,horizontal,lo,hi) := (3600,radius150,radius150_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_72 (dictionary,horizontal,lo,hi) := (3601,radius151,radius151_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_73 (dictionary,horizontal,lo,hi) := (3602,radius152,radius152_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_74 (dictionary,horizontal,lo,hi) := (3603,radius153,radius153_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_75 (dictionary,horizontal,lo,hi) := (3604,radius154,radius154_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_76 (dictionary,horizontal,lo,hi) := (3605,radius155,radius155_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_77 (dictionary,horizontal,lo,hi) := (3606,radius156,radius156_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_78 (dictionary,horizontal,lo,hi) := (3607,radius157,radius157_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_79 (dictionary,horizontal,lo,hi) := (3608,radius158,radius158_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_80 (dictionary,horizontal,lo,hi) := (3609,radius159,radius159_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_81 (dictionary,horizontal,lo,hi) := (3610,radius160,radius160_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_82 (dictionary,horizontal,lo,hi) := (3611,radius161,radius161_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_83 (dictionary,horizontal,lo,hi) := (3612,radius162,radius162_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_84 (dictionary,horizontal,lo,hi) := (3613,radius163,radius163_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_85 (dictionary,horizontal,lo,hi) := (3614,radius164,radius164_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_86 (dictionary,horizontal,lo,hi) := (3615,radius165,radius165_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_87 (dictionary,horizontal,lo,hi) := (3616,radius166,radius166_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_88 (dictionary,horizontal,lo,hi) := (3617,radius167,radius167_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_89 (dictionary,horizontal,lo,hi) := (3618,radius168,radius168_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_90 (dictionary,horizontal,lo,hi) := (3619,radius169,radius169_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_91 (dictionary,horizontal,lo,hi) := (3620,radius170,radius170_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_92 (dictionary,horizontal,lo,hi) := (3621,radius171,radius171_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_93 (dictionary,horizontal,lo,hi) := (3622,radius172,radius172_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_94 (dictionary,horizontal,lo,hi) := (3623,radius173,radius173_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_95 (dictionary,horizontal,lo,hi) := (3624,radius174,radius174_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_96 (dictionary,horizontal,lo,hi) := (3625,radius175,radius175_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_97 (dictionary,horizontal,lo,hi) := (3626,radius176,radius176_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_98 (dictionary,horizontal,lo,hi) := (3627,radius177,radius177_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_99 (dictionary,horizontal,lo,hi) := (3628,radius178,radius178_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_100 (dictionary,horizontal,lo,hi) := (3629,radius179,radius179_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_101 (dictionary,horizontal,lo,hi) := (3630,radius180,radius180_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_102 (dictionary,horizontal,lo,hi) := (3631,radius181,radius181_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_103 (dictionary,horizontal,lo,hi) := (3632,radius182,radius182_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_104 (dictionary,horizontal,lo,hi) := (3633,radius183,radius183_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_105 (dictionary,horizontal,lo,hi) := (3634,radius184,radius184_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_106 (dictionary,horizontal,lo,hi) := (3635,radius185,radius185_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_107 (dictionary,horizontal,lo,hi) := (3636,radius186,radius186_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_108 (dictionary,horizontal,lo,hi) := (3637,radius187,radius187_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_109 (dictionary,horizontal,lo,hi) := (3638,radius188,radius188_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_110 (dictionary,horizontal,lo,hi) := (3639,radius189,radius189_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_111 (dictionary,horizontal,lo,hi) := (3640,radius190,radius190_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_112 (dictionary,horizontal,lo,hi) := (3641,radius191,radius191_checked,[.single 6, .single 3])
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
    neighbor2_108, neighbor2_109, neighbor2_110, neighbor2_111, neighbor2_112]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout979Domain8_0Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (10388,radius64,radius64_checked,chord_close%(⟨[0,6],[(1,0),(200,6)]⟩),chord_keep%(10212,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (10389,radius65,radius65_checked,chord_close%(⟨[0,6],[(4,0),(1,6)]⟩),chord_keep%(10213,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (10390,radius66,radius66_checked,chord_close%(⟨[0,6],[(1,0),(2,6)]⟩),chord_keep%(10214,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (10391,radius67,radius67_checked,chord_close%(⟨[0,6],[(1,0),(1,6)]⟩),chord_keep%(10215,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (10392,radius68,radius68_checked,chord_close%(⟨[0,6],[(1,0),(10,6)]⟩),chord_keep%(10216,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (10393,radius69,radius69_checked,chord_close%(⟨[0,6],[(4,0),(1,6)]⟩),chord_keep%(10217,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (10394,radius70,radius70_checked,chord_close%(⟨[0,6],[(1,0),(1,6)]⟩),chord_keep%(10218,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (10395,radius71,radius71_checked,chord_close%(⟨[0,6],[(1,0),(2,6)]⟩),chord_keep%(10219,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (10396,radius72,radius72_checked,chord_close%(⟨[0,6],[(2,0),(125,6)]⟩),chord_keep%(10220,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (10397,radius73,radius73_checked,chord_close%(⟨[0,6],[(1,0),(2,6)]⟩),chord_keep%(10221,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (10398,radius74,radius74_checked,chord_close%(⟨[0,6],[(1,0),(8,6)]⟩),chord_keep%(10222,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (10399,radius75,radius75_checked,chord_close%(⟨[0,5],[(4,0),(1,5)]⟩),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (10400,radius76,radius76_checked,chord_close%(⟨[0,5],[(8,0),(1,5)]⟩),chord_close%(⟨[0,3],[(8,0),(1,3)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (10401,radius77,radius77_checked,chord_close%(⟨[0,5],[(1,0),(5,5)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (10402,radius78,radius78_checked,chord_close%(⟨[0,5],[(64,0),(5,5)]⟩),chord_close%(⟨[0,3],[(8,0),(1,3)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (10403,radius79,radius79_checked,chord_close%(⟨[0,5],[(16,0),(5,5)]⟩),chord_close%(⟨[0,3],[(8,0),(1,3)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (10404,radius80,radius80_checked,chord_close%(⟨[0,5],[(2,0),(1,5)]⟩),chord_close%(⟨[0,3],[(1,0),(50,3)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (10405,radius81,radius81_checked,chord_close%(⟨[0,5],[(64,0),(1,5)]⟩),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (10406,radius82,radius82_checked,chord_close%(⟨[0,5],[(1,0),(1,5)]⟩),chord_close%(⟨[0,3],[(1,0),(10,3)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (10407,radius83,radius83_checked,chord_close%(⟨[0,5],[(1,0),(1,5)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (10408,radius84,radius84_checked,chord_close%(⟨[0,5],[(1,0),(1,5)]⟩),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (10409,radius85,radius85_checked,chord_close%(⟨[0,5],[(1,0),(1,5)]⟩),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (10410,radius86,radius86_checked,chord_close%(⟨[0,5],[(2,0),(1,5)]⟩),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (10411,radius87,radius87_checked,chord_close%(⟨[0,5],[(2,0),(1,5)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (10412,radius88,radius88_checked,chord_close%(⟨[0,5],[(4,0),(1,5)]⟩),chord_close%(⟨[0,3],[(4,0),(1,3)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (10413,radius89,radius89_checked,chord_close%(⟨[0,5],[(1,0),(2,5)]⟩),chord_close%(⟨[0,3],[(1,0),(2,3)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (10414,radius90,radius90_checked,chord_close%(⟨[0,5],[(5,0),(2,5)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (10415,radius91,radius91_checked,chord_close%(⟨[0,5],[(2,0),(1,5)]⟩),chord_close%(⟨[0,3],[(5,0),(1,3)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (10416,radius92,radius92_checked,chord_close%(⟨[0,5],[(1,0),(4,5)]⟩),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (10417,radius93,radius93_checked,chord_close%(⟨[0,6],[(5,0),(2,6)]⟩),chord_keep%(10223,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 0, .single 0, .single 3, .single 2, .single 5, .copy 11]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (10418,radius94,radius94_checked,chord_close%(⟨[0,7],[(16,0),(1,7)]⟩),chord_keep%(10224,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (10419,radius95,radius95_checked,chord_close%(⟨[0,7],[(1,0),(16,7)]⟩),chord_keep%(10225,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (10420,radius96,radius96_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(10226,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 4, .single 2, .single 7, .copy 13]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (10421,radius97,radius97_checked,chord_close%(⟨[0,8],[(4,0),(1,8)]⟩),chord_keep%(10227,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 0, .single 0, .single 4, .single 2, .single 7, .copy 13]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (10422,radius98,radius98_checked,chord_close%(⟨[0,7],[(5,0),(16,7)]⟩),chord_keep%(10228,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (10423,radius99,radius99_checked,chord_close%(⟨[0,7],[(4,0),(5,7)]⟩),chord_keep%(10229,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (10424,radius100,radius100_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10230,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (10425,radius101,radius101_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_keep%(10231,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (10426,radius102,radius102_checked,chord_close%(⟨[0,7],[(1,0),(128,7)]⟩),chord_keep%(10232,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (10427,radius103,radius103_checked,chord_close%(⟨[0,7],[(1,0),(10,7)]⟩),chord_keep%(10233,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (10428,radius104,radius104_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_keep%(10234,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (10429,radius105,radius105_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10235,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (10430,radius106,radius106_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10236,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (10431,radius107,radius107_checked,chord_close%(⟨[0,7],[(5,0),(2,7)]⟩),chord_keep%(10237,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (10432,radius108,radius108_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(10238,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (10433,radius109,radius109_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10239,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (10434,radius110,radius110_checked,chord_close%(⟨[0,7],[(1,0),(5,7)]⟩),chord_keep%(10240,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (10435,radius111,radius111_checked,chord_close%(⟨[0,7],[(1,0),(5,7)]⟩),chord_keep%(10241,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (10436,radius112,radius112_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(10242,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (10437,radius113,radius113_checked,chord_close%(⟨[0,7],[(5,0),(1,7)]⟩),chord_keep%(10243,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (10438,radius114,radius114_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(10244,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (10439,radius115,radius115_checked,chord_close%(⟨[0,7],[(1,0),(128,7)]⟩),chord_keep%(10245,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (10440,radius116,radius116_checked,chord_close%(⟨[0,7],[(16,0),(1,7)]⟩),chord_keep%(10246,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (10441,radius117,radius117_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10247,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (10442,radius118,radius118_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10248,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (10443,radius119,radius119_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10249,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (10444,radius120,radius120_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10250,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (10445,radius121,radius121_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10251,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (10446,radius122,radius122_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10252,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (10447,radius123,radius123_checked,chord_close%(⟨[0,7],[(8,0),(5,7)]⟩),chord_keep%(10253,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 6, .copy 12]))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (10448,radius124,radius124_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10254,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (10449,radius125,radius125_checked,chord_close%(⟨[0,7],[(8,0),(1,7)]⟩),chord_keep%(10255,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (10450,radius126,radius126_checked,chord_close%(⟨[0,7],[(20,0),(1,7)]⟩),chord_keep%(10256,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (10451,radius127,radius127_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10257,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan64 (dictionary,horizontal,lo,hi) := (10452,radius128,radius128_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10258,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan65 (dictionary,horizontal,lo,hi) := (10453,radius129,radius129_checked,chord_close%(⟨[0,7],[(50,0),(1,7)]⟩),chord_keep%(10259,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan66 (dictionary,horizontal,lo,hi) := (10454,radius130,radius130_checked,chord_close%(⟨[0,7],[(125,0),(1,7)]⟩),chord_keep%(10260,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan67 (dictionary,horizontal,lo,hi) := (10455,radius131,radius131_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10261,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan68 (dictionary,horizontal,lo,hi) := (10456,radius132,radius132_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(10262,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan69 (dictionary,horizontal,lo,hi) := (10457,radius133,radius133_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10263,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan70 (dictionary,horizontal,lo,hi) := (10458,radius134,radius134_checked,chord_close%(⟨[0,7],[(5,0),(8,7)]⟩),chord_keep%(10264,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan71 (dictionary,horizontal,lo,hi) := (10459,radius135,radius135_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10265,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan72 (dictionary,horizontal,lo,hi) := (10460,radius136,radius136_checked,chord_close%(⟨[0,7],[(20,0),(1,7)]⟩),chord_keep%(10266,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan73 (dictionary,horizontal,lo,hi) := (10461,radius137,radius137_checked,chord_close%(⟨[0,7],[(5,0),(8,7)]⟩),chord_keep%(10267,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan74 (dictionary,horizontal,lo,hi) := (10462,radius138,radius138_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10268,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan75 (dictionary,horizontal,lo,hi) := (10463,radius139,radius139_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10269,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan76 (dictionary,horizontal,lo,hi) := (10464,radius140,radius140_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10270,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan77 (dictionary,horizontal,lo,hi) := (10465,radius141,radius141_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10271,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan78 (dictionary,horizontal,lo,hi) := (10466,radius142,radius142_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(10272,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan79 (dictionary,horizontal,lo,hi) := (10467,radius143,radius143_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10273,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan80 (dictionary,horizontal,lo,hi) := (10468,radius144,radius144_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(10274,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan81 (dictionary,horizontal,lo,hi) := (10469,radius145,radius145_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10275,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan82 (dictionary,horizontal,lo,hi) := (10470,radius146,radius146_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10276,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan83 (dictionary,horizontal,lo,hi) := (10471,radius147,radius147_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(10277,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan84 (dictionary,horizontal,lo,hi) := (10472,radius148,radius148_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10278,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan85 (dictionary,horizontal,lo,hi) := (10473,radius149,radius149_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(10279,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan86 (dictionary,horizontal,lo,hi) := (10474,radius150,radius150_checked,chord_close%(⟨[0,7],[(1,0),(128,7)]⟩),chord_keep%(10280,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan87 (dictionary,horizontal,lo,hi) := (10475,radius151,radius151_checked,chord_close%(⟨[0,7],[(10,0),(1,7)]⟩),chord_keep%(10281,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan88 (dictionary,horizontal,lo,hi) := (10476,radius152,radius152_checked,chord_close%(⟨[0,7],[(10,0),(1,7)]⟩),chord_keep%(10282,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan89 (dictionary,horizontal,lo,hi) := (10477,radius153,radius153_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10283,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan90 (dictionary,horizontal,lo,hi) := (10478,radius154,radius154_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(10284,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan91 (dictionary,horizontal,lo,hi) := (10479,radius155,radius155_checked,chord_close%(⟨[0,7],[(2,0),(625,7)]⟩),chord_keep%(10285,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan92 (dictionary,horizontal,lo,hi) := (10480,radius156,radius156_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10286,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan93 (dictionary,horizontal,lo,hi) := (10481,radius157,radius157_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10287,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan94 (dictionary,horizontal,lo,hi) := (10482,radius158,radius158_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10288,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan95 (dictionary,horizontal,lo,hi) := (10483,radius159,radius159_checked,chord_close%(⟨[0,7],[(20,0),(1,7)]⟩),chord_keep%(10289,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan96 (dictionary,horizontal,lo,hi) := (10484,radius160,radius160_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_keep%(10290,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan97 (dictionary,horizontal,lo,hi) := (10485,radius161,radius161_checked,chord_close%(⟨[0,7],[(5,0),(1,7)]⟩),chord_keep%(10291,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan98 (dictionary,horizontal,lo,hi) := (10486,radius162,radius162_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10292,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan99 (dictionary,horizontal,lo,hi) := (10487,radius163,radius163_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(10293,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan100 (dictionary,horizontal,lo,hi) := (10488,radius164,radius164_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_keep%(10294,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan101 (dictionary,horizontal,lo,hi) := (10489,radius165,radius165_checked,chord_close%(⟨[0,7],[(4,0),(5,7)]⟩),chord_keep%(10295,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan102 (dictionary,horizontal,lo,hi) := (10490,radius166,radius166_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_keep%(10296,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan103 (dictionary,horizontal,lo,hi) := (10491,radius167,radius167_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10297,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan104 (dictionary,horizontal,lo,hi) := (10492,radius168,radius168_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10298,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan105 (dictionary,horizontal,lo,hi) := (10493,radius169,radius169_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10299,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan106 (dictionary,horizontal,lo,hi) := (10494,radius170,radius170_checked,chord_close%(⟨[0,7],[(1,0),(5,7)]⟩),chord_keep%(10300,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan107 (dictionary,horizontal,lo,hi) := (10495,radius171,radius171_checked,chord_close%(⟨[0,7],[(100,0),(1,7)]⟩),chord_keep%(10301,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan108 (dictionary,horizontal,lo,hi) := (10496,radius172,radius172_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10302,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan109 (dictionary,horizontal,lo,hi) := (10497,radius173,radius173_checked,chord_close%(⟨[0,7],[(8,0),(1,7)]⟩),chord_keep%(10303,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan110 (dictionary,horizontal,lo,hi) := (10498,radius174,radius174_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10304,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan111 (dictionary,horizontal,lo,hi) := (10499,radius175,radius175_checked,chord_close%(⟨[0,7],[(1,0),(10,7)]⟩),chord_keep%(10305,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan112 (dictionary,horizontal,lo,hi) := (10500,radius176,radius176_checked,chord_close%(⟨[0,7],[(1,0),(64,7)]⟩),chord_keep%(10306,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan113 (dictionary,horizontal,lo,hi) := (10501,radius177,radius177_checked,chord_close%(⟨[0,7],[(25,0),(2,7)]⟩),chord_keep%(10307,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan114 (dictionary,horizontal,lo,hi) := (10502,radius178,radius178_checked,chord_close%(⟨[0,7],[(1,0),(5,7)]⟩),chord_keep%(10308,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan115 (dictionary,horizontal,lo,hi) := (10503,radius179,radius179_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(10309,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan116 (dictionary,horizontal,lo,hi) := (10504,radius180,radius180_checked,chord_close%(⟨[0,7],[(8,0),(1,7)]⟩),chord_keep%(10310,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan117 (dictionary,horizontal,lo,hi) := (10505,radius181,radius181_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(10311,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan118 (dictionary,horizontal,lo,hi) := (10506,radius182,radius182_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(10312,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan119 (dictionary,horizontal,lo,hi) := (10507,radius183,radius183_checked,chord_close%(⟨[0,7],[(20,0),(1,7)]⟩),chord_keep%(10313,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 12]))
checked_chord_plan plan120 (dictionary,horizontal,lo,hi) := (10508,radius184,radius184_checked,chord_close%(⟨[0,7],[(1,0),(256,7)]⟩),chord_keep%(10314,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .pair 0 2, .single 6, .copy 12]))
checked_chord_plan plan121 (dictionary,horizontal,lo,hi) := (10509,radius185,radius185_checked,chord_close%(⟨[0,7],[(5,0),(1,7)]⟩),chord_keep%(10315,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .pair 0 2, .single 6, .copy 12]))
checked_chord_plan plan122 (dictionary,horizontal,lo,hi) := (10510,radius186,radius186_checked,chord_close%(⟨[0,7],[(1,0),(125,7)]⟩),chord_keep%(10316,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .pair 0 2, .single 6, .copy 12]))
checked_chord_plan plan123 (dictionary,horizontal,lo,hi) := (10511,radius187,radius187_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_keep%(10317,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 6, .single 0, .single 0, .single 4, .pair 0 2, .single 6, .copy 12]))
checked_chord_plan plan124 (dictionary,horizontal,lo,hi) := (10512,radius188,radius188_checked,chord_close%(⟨[0,6],[(2,0),(5,6)]⟩),chord_keep%(10318,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 4, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan125 (dictionary,horizontal,lo,hi) := (10513,radius189,radius189_checked,chord_close%(⟨[0,6],[(10,0),(1,6)]⟩),chord_keep%(10319,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 4, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan126 (dictionary,horizontal,lo,hi) := (10514,radius190,radius190_checked,chord_close%(⟨[0,6],[(2,0),(1,6)]⟩),chord_keep%(10320,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 4, .pair 0 2, .single 5, .copy 11]))
checked_chord_plan plan127 (dictionary,horizontal,lo,hi) := (10515,radius191,radius191_checked,chord_close%(⟨[0,6],[(1,0),(200,6)]⟩),chord_keep%(10321,[.pair 0 2, .pair 2 3, .single 3, .single 4, .single 5, .single 0, .single 0, .single 4, .pair 0 2, .single 5, .copy 11]))
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

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout979Domain4_4Ids := by rfl
def outputIds : List (Fin poseCount) := [10212,10213,10214,10215,10216,10217,10218,10219,10220,10221,10222,10223,10224,10225,10226,10227,10228,10229,10230,10231,10232,10233,10234,10235,10236,10237,10238,10239,10240,10241,10242,10243,10244,10245,10246,10247,10248,10249,10250,10251,10252,10253,10254,10255,10256,10257,10258,10259,10260,10261,10262,10263,10264,10265,10266,10267,10268,10269,10270,10271,10272,10273,10274,10275,10276,10277,10278,10279,10280,10281,10282,10283,10284,10285,10286,10287,10288,10289,10290,10291,10292,10293,10294,10295,10296,10297,10298,10299,10300,10301,10302,10303,10304,10305,10306,10307,10308,10309,10310,10311,10312,10313,10314,10315,10316,10317,10318,10319,10320,10321]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout979Domain4_28Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout979Domain4_28Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout979Domain4_4 (q 0))
    (h0 : OrientedPoseCovered continuousScout979Domain0_27 (q 1))
    (h1 : OrientedPoseCovered continuousScout979Domain1_1 (q 2))
    (h2 : OrientedPoseCovered continuousScout979Domain8_0 (q 3))
    : OrientedPoseCovered continuousScout979Domain4_28 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout979Domain4_4Ids continuousScout979Domain4_28Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain0_27Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain1_1Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain8_0Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![192,1,2,4096]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout979Domain4_4 (p.square (ownerIndex p 192)))
    (h0 : OrientedPoseCovered continuousScout979Domain0_27 (p.square (ownerIndex p 1)))
    (h1 : OrientedPoseCovered continuousScout979Domain1_1 (p.square (ownerIndex p 2)))
    (h2 : OrientedPoseCovered continuousScout979Domain8_0 (p.square (ownerIndex p 4096)))
    : OrientedPoseCovered continuousScout979Domain4_28 (p.square (ownerIndex p 192)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout979Domain4_4 continuousScout979Domain4_28
    ![continuousScout979Domain0_27,continuousScout979Domain1_1,continuousScout979Domain8_0]
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
end N12Compact.Preservation.Chords.C979Step27

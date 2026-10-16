import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C717

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C717Step17
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C717

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (83109251/50000000)
def hi : ℚ := (167797227/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (4099,radius64,radius64_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (4100,radius65,radius65_checked,[.single 9, .single 2])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (4101,radius66,radius66_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (4102,radius67,radius67_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (4103,radius68,radius68_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (4104,radius69,radius69_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (4105,radius70,radius70_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (4106,radius71,radius71_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (4107,radius72,radius72_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (4108,radius73,radius73_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (4109,radius74,radius74_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (4110,radius75,radius75_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (4111,radius76,radius76_checked,[.single 6, .single 1])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (4112,radius77,radius77_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (4113,radius159,radius159_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (4114,radius160,radius160_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (4115,radius161,radius161_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (4116,radius162,radius162_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (4117,radius163,radius163_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (4118,radius164,radius164_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (4119,radius165,radius165_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (4120,radius166,radius166_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (4121,radius167,radius167_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (4122,radius168,radius168_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (4123,radius169,radius169_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (4124,radius170,radius170_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (4125,radius171,radius171_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (4126,radius172,radius172_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (4127,radius173,radius173_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_29 (dictionary,horizontal,lo,hi) := (4128,radius174,radius174_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_30 (dictionary,horizontal,lo,hi) := (4129,radius175,radius175_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_31 (dictionary,horizontal,lo,hi) := (4130,radius176,radius176_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_32 (dictionary,horizontal,lo,hi) := (4131,radius177,radius177_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_33 (dictionary,horizontal,lo,hi) := (4132,radius178,radius178_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_34 (dictionary,horizontal,lo,hi) := (4133,radius179,radius179_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_35 (dictionary,horizontal,lo,hi) := (4134,radius180,radius180_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_36 (dictionary,horizontal,lo,hi) := (4135,radius181,radius181_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_37 (dictionary,horizontal,lo,hi) := (4136,radius182,radius182_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_38 (dictionary,horizontal,lo,hi) := (4137,radius183,radius183_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_39 (dictionary,horizontal,lo,hi) := (4138,radius184,radius184_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_40 (dictionary,horizontal,lo,hi) := (4139,radius185,radius185_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_41 (dictionary,horizontal,lo,hi) := (4140,radius186,radius186_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_42 (dictionary,horizontal,lo,hi) := (4141,radius187,radius187_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_43 (dictionary,horizontal,lo,hi) := (4142,radius188,radius188_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_44 (dictionary,horizontal,lo,hi) := (4143,radius189,radius189_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_45 (dictionary,horizontal,lo,hi) := (4144,radius190,radius190_checked,[.single 7, .single 2])
checked_chord_neighbor neighbor0_46 (dictionary,horizontal,lo,hi) := (4145,radius191,radius191_checked,[.single 7, .single 2])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28, neighbor0_29, neighbor0_30, neighbor0_31, neighbor0_32, neighbor0_33, neighbor0_34, neighbor0_35,
    neighbor0_36, neighbor0_37, neighbor0_38, neighbor0_39, neighbor0_40, neighbor0_41, neighbor0_42, neighbor0_43, neighbor0_44, neighbor0_45, neighbor0_46]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout717Domain0_15Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (5643,radius64,radius64_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (5644,radius65,radius65_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (5645,radius74,radius74_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (5646,radius75,radius75_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (5647,radius76,radius76_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (5648,radius77,radius77_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (5649,radius78,radius78_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (5650,radius79,radius79_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (5651,radius80,radius80_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (5652,radius190,radius190_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (5653,radius191,radius191_checked,[.single 8, .single 3])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout717Domain7_11Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (2308,radius64,radius64_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (2309,radius65,radius65_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (2310,radius66,radius66_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (2311,radius67,radius67_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (2312,radius68,radius68_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (2313,radius69,radius69_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (2314,radius70,radius70_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (2315,radius71,radius71_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (2316,radius72,radius72_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (2317,radius73,radius73_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (2318,radius74,radius74_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (2319,radius75,radius75_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (2320,radius76,radius76_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (2321,radius77,radius77_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (2322,radius78,radius78_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (2323,radius79,radius79_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (2324,radius80,radius80_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (2325,radius81,radius81_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (2326,radius82,radius82_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (2327,radius83,radius83_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (2328,radius84,radius84_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (2329,radius85,radius85_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (2330,radius86,radius86_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (2331,radius87,radius87_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (2332,radius88,radius88_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (2333,radius89,radius89_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (2334,radius90,radius90_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_27 (dictionary,horizontal,lo,hi) := (2335,radius91,radius91_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_28 (dictionary,horizontal,lo,hi) := (2336,radius92,radius92_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_29 (dictionary,horizontal,lo,hi) := (2337,radius93,radius93_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_30 (dictionary,horizontal,lo,hi) := (2338,radius94,radius94_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_31 (dictionary,horizontal,lo,hi) := (2339,radius95,radius95_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_32 (dictionary,horizontal,lo,hi) := (2340,radius96,radius96_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_33 (dictionary,horizontal,lo,hi) := (2341,radius97,radius97_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_34 (dictionary,horizontal,lo,hi) := (2342,radius98,radius98_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_35 (dictionary,horizontal,lo,hi) := (2343,radius99,radius99_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_36 (dictionary,horizontal,lo,hi) := (2344,radius100,radius100_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_37 (dictionary,horizontal,lo,hi) := (2345,radius101,radius101_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_38 (dictionary,horizontal,lo,hi) := (2346,radius102,radius102_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_39 (dictionary,horizontal,lo,hi) := (2347,radius103,radius103_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_40 (dictionary,horizontal,lo,hi) := (2348,radius104,radius104_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_41 (dictionary,horizontal,lo,hi) := (2349,radius105,radius105_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_42 (dictionary,horizontal,lo,hi) := (2350,radius106,radius106_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor2_43 (dictionary,horizontal,lo,hi) := (2351,radius121,radius121_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_44 (dictionary,horizontal,lo,hi) := (2352,radius122,radius122_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_45 (dictionary,horizontal,lo,hi) := (2353,radius123,radius123_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_46 (dictionary,horizontal,lo,hi) := (2354,radius124,radius124_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_47 (dictionary,horizontal,lo,hi) := (2355,radius125,radius125_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_48 (dictionary,horizontal,lo,hi) := (2356,radius126,radius126_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_49 (dictionary,horizontal,lo,hi) := (2357,radius127,radius127_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_50 (dictionary,horizontal,lo,hi) := (2358,radius128,radius128_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_51 (dictionary,horizontal,lo,hi) := (2359,radius129,radius129_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_52 (dictionary,horizontal,lo,hi) := (2360,radius130,radius130_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_53 (dictionary,horizontal,lo,hi) := (2361,radius131,radius131_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_54 (dictionary,horizontal,lo,hi) := (2362,radius132,radius132_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_55 (dictionary,horizontal,lo,hi) := (2363,radius133,radius133_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_56 (dictionary,horizontal,lo,hi) := (2364,radius134,radius134_checked,[.single 7, .single 4])
checked_chord_neighbor neighbor2_57 (dictionary,horizontal,lo,hi) := (2365,radius135,radius135_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_58 (dictionary,horizontal,lo,hi) := (2366,radius136,radius136_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_59 (dictionary,horizontal,lo,hi) := (2367,radius137,radius137_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_60 (dictionary,horizontal,lo,hi) := (2368,radius138,radius138_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_61 (dictionary,horizontal,lo,hi) := (2369,radius139,radius139_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_62 (dictionary,horizontal,lo,hi) := (2370,radius140,radius140_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_63 (dictionary,horizontal,lo,hi) := (2371,radius141,radius141_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_64 (dictionary,horizontal,lo,hi) := (2372,radius142,radius142_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_65 (dictionary,horizontal,lo,hi) := (2373,radius143,radius143_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_66 (dictionary,horizontal,lo,hi) := (2374,radius144,radius144_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_67 (dictionary,horizontal,lo,hi) := (2375,radius145,radius145_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_68 (dictionary,horizontal,lo,hi) := (2376,radius146,radius146_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_69 (dictionary,horizontal,lo,hi) := (2377,radius147,radius147_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_70 (dictionary,horizontal,lo,hi) := (2378,radius148,radius148_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_71 (dictionary,horizontal,lo,hi) := (2379,radius149,radius149_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_72 (dictionary,horizontal,lo,hi) := (2380,radius150,radius150_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_73 (dictionary,horizontal,lo,hi) := (2381,radius151,radius151_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_74 (dictionary,horizontal,lo,hi) := (2382,radius152,radius152_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_75 (dictionary,horizontal,lo,hi) := (2383,radius153,radius153_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_76 (dictionary,horizontal,lo,hi) := (2384,radius154,radius154_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_77 (dictionary,horizontal,lo,hi) := (4149,radius155,radius155_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_78 (dictionary,horizontal,lo,hi) := (4150,radius156,radius156_checked,[.single 8, .single 3])
checked_chord_neighbor neighbor2_79 (dictionary,horizontal,lo,hi) := (2387,radius157,radius157_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_80 (dictionary,horizontal,lo,hi) := (2388,radius158,radius158_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_81 (dictionary,horizontal,lo,hi) := (2389,radius159,radius159_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_82 (dictionary,horizontal,lo,hi) := (2390,radius160,radius160_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_83 (dictionary,horizontal,lo,hi) := (2391,radius161,radius161_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_84 (dictionary,horizontal,lo,hi) := (2392,radius162,radius162_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_85 (dictionary,horizontal,lo,hi) := (2393,radius163,radius163_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_86 (dictionary,horizontal,lo,hi) := (2394,radius164,radius164_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_87 (dictionary,horizontal,lo,hi) := (2395,radius165,radius165_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_88 (dictionary,horizontal,lo,hi) := (2396,radius166,radius166_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_89 (dictionary,horizontal,lo,hi) := (2397,radius167,radius167_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_90 (dictionary,horizontal,lo,hi) := (2398,radius168,radius168_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_91 (dictionary,horizontal,lo,hi) := (2399,radius169,radius169_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_92 (dictionary,horizontal,lo,hi) := (2400,radius170,radius170_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_93 (dictionary,horizontal,lo,hi) := (2401,radius171,radius171_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_94 (dictionary,horizontal,lo,hi) := (2402,radius172,radius172_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_95 (dictionary,horizontal,lo,hi) := (2403,radius173,radius173_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_96 (dictionary,horizontal,lo,hi) := (2404,radius174,radius174_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_97 (dictionary,horizontal,lo,hi) := (2405,radius175,radius175_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_98 (dictionary,horizontal,lo,hi) := (2406,radius176,radius176_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_99 (dictionary,horizontal,lo,hi) := (2407,radius177,radius177_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_100 (dictionary,horizontal,lo,hi) := (2408,radius178,radius178_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_101 (dictionary,horizontal,lo,hi) := (2409,radius179,radius179_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_102 (dictionary,horizontal,lo,hi) := (2410,radius180,radius180_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_103 (dictionary,horizontal,lo,hi) := (2411,radius181,radius181_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_104 (dictionary,horizontal,lo,hi) := (2412,radius182,radius182_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor2_105 (dictionary,horizontal,lo,hi) := (2413,radius183,radius183_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_106 (dictionary,horizontal,lo,hi) := (2414,radius184,radius184_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_107 (dictionary,horizontal,lo,hi) := (2415,radius185,radius185_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_108 (dictionary,horizontal,lo,hi) := (2416,radius186,radius186_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_109 (dictionary,horizontal,lo,hi) := (2417,radius187,radius187_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_110 (dictionary,horizontal,lo,hi) := (2418,radius188,radius188_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_111 (dictionary,horizontal,lo,hi) := (2419,radius189,radius189_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_112 (dictionary,horizontal,lo,hi) := (2420,radius190,radius190_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor2_113 (dictionary,horizontal,lo,hi) := (2421,radius191,radius191_checked,[.single 8, .single 4])
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
    neighbor2_108, neighbor2_109, neighbor2_110, neighbor2_111, neighbor2_112, neighbor2_113]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout717Domain11_0Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (5470,radius64,radius64_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_close%(⟨[0,5],[(64,0),(1,5)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (5471,radius65,radius65_checked,chord_close%(⟨[0,8],[(4,0),(1,8)]⟩),chord_close%(⟨[0,4],[(25,0),(1,4)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (5472,radius72,radius72_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(5259,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .pair 3 6, .single 0, .single 0, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (5473,radius73,radius73_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(5260,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .pair 3 6, .single 0, .single 0, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (5474,radius74,radius74_checked,chord_close%(⟨[0,7],[(1,0),(62500,7)]⟩),chord_keep%(5261,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .pair 3 6, .single 0, .single 0, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (5475,radius75,radius75_checked,chord_close%(⟨[0,8],[(400,0),(1,8)]⟩),chord_keep%(5262,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (5476,radius76,radius76_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_keep%(5263,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (5477,radius77,radius77_checked,chord_close%(⟨[0,8],[(1,0),(40,8)]⟩),chord_keep%(5264,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (5478,radius78,radius78_checked,chord_close%(⟨[0,8],[(2,0),(5,8)]⟩),chord_keep%(5265,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (5479,radius79,radius79_checked,chord_close%(⟨[0,8],[(20,0),(1,8)]⟩),chord_keep%(5266,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (5480,radius80,radius80_checked,chord_close%(⟨[0,8],[(8,0),(1,8)]⟩),chord_keep%(5267,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (5481,radius81,radius81_checked,chord_close%(⟨[0,8],[(1,0),(40,8)]⟩),chord_keep%(5268,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (5482,radius82,radius82_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_keep%(5269,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (5483,radius83,radius83_checked,chord_close%(⟨[0,8],[(1,0),(2,8)]⟩),chord_keep%(5270,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (5484,radius84,radius84_checked,chord_close%(⟨[0,8],[(1,0),(4,8)]⟩),chord_keep%(5271,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (5485,radius85,radius85_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_keep%(5272,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (5486,radius86,radius86_checked,chord_close%(⟨[0,8],[(32,0),(1,8)]⟩),chord_keep%(5273,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (5487,radius87,radius87_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(5274,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (5488,radius140,radius140_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(8,4)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (5489,radius141,radius141_checked,chord_close%(⟨[0,8],[(5,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(25,4)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (5490,radius142,radius142_checked,chord_close%(⟨[0,8],[(5,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (5491,radius143,radius143_checked,chord_close%(⟨[0,8],[(1,0),(25,8)]⟩),chord_close%(⟨[0,4],[(4,0),(1,4)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (5492,radius144,radius144_checked,chord_close%(⟨[0,8],[(256,0),(5,8)]⟩),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (5493,radius145,radius145_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(128,4)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (5494,radius146,radius146_checked,chord_close%(⟨[0,7],[(10,0),(1,7)]⟩),chord_close%(⟨[0,3],[(1,0),(25,3)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (5495,radius190,radius190_checked,chord_close%(⟨[0,8],[(5,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(64,4)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (5496,radius191,radius191_checked,chord_close%(⟨[0,9],[(1,0),(2,9)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout717Domain6_8Ids := by rfl
def outputIds : List (Fin poseCount) := [5259,5260,5261,5262,5263,5264,5265,5266,5267,5268,5269,5270,5271,5272,5273,5274]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout717Domain6_18Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout717Domain6_18Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout717Domain6_8 (q 0))
    (h0 : OrientedPoseCovered continuousScout717Domain0_15 (q 1))
    (h1 : OrientedPoseCovered continuousScout717Domain7_11 (q 2))
    (h2 : OrientedPoseCovered continuousScout717Domain11_0 (q 3))
    : OrientedPoseCovered continuousScout717Domain6_18 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout717Domain6_8Ids continuousScout717Domain6_18Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout717Domain0_15Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout717Domain7_11Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout717Domain11_0Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![768,1,3072,32768]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout717Domain6_8 (p.square (ownerIndex p 768)))
    (h0 : OrientedPoseCovered continuousScout717Domain0_15 (p.square (ownerIndex p 1)))
    (h1 : OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)))
    (h2 : OrientedPoseCovered continuousScout717Domain11_0 (p.square (ownerIndex p 32768)))
    : OrientedPoseCovered continuousScout717Domain6_18 (p.square (ownerIndex p 768)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout717Domain6_8 continuousScout717Domain6_18
    ![continuousScout717Domain0_15,continuousScout717Domain7_11,continuousScout717Domain11_0]
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
end N12Compact.Preservation.Chords.C717Step17

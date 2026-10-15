import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C979

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C979Step24
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C979

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (48264593/20000000)
def hi : ℚ := (262167007/100000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (11484,radius148,radius148_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (11485,radius149,radius149_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (11486,radius150,radius150_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (11487,radius151,radius151_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (11488,radius152,radius152_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (11489,radius153,radius153_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (11490,radius154,radius154_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (11491,radius155,radius155_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (11492,radius156,radius156_checked,[.single 7, .single 3])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout979Domain6_24Ids := by rfl

checked_chord_neighbor neighbor1_0 (dictionary,horizontal,lo,hi) := (11970,radius64,radius64_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_1 (dictionary,horizontal,lo,hi) := (11971,radius65,radius65_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_2 (dictionary,horizontal,lo,hi) := (11972,radius66,radius66_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_3 (dictionary,horizontal,lo,hi) := (11973,radius67,radius67_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_4 (dictionary,horizontal,lo,hi) := (11974,radius68,radius68_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_5 (dictionary,horizontal,lo,hi) := (11975,radius69,radius69_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_6 (dictionary,horizontal,lo,hi) := (11976,radius70,radius70_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_7 (dictionary,horizontal,lo,hi) := (11977,radius71,radius71_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_8 (dictionary,horizontal,lo,hi) := (11978,radius72,radius72_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_9 (dictionary,horizontal,lo,hi) := (11979,radius73,radius73_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_10 (dictionary,horizontal,lo,hi) := (11980,radius74,radius74_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_11 (dictionary,horizontal,lo,hi) := (11981,radius75,radius75_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_12 (dictionary,horizontal,lo,hi) := (11982,radius76,radius76_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_13 (dictionary,horizontal,lo,hi) := (11983,radius77,radius77_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_14 (dictionary,horizontal,lo,hi) := (11984,radius78,radius78_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_15 (dictionary,horizontal,lo,hi) := (11985,radius79,radius79_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_16 (dictionary,horizontal,lo,hi) := (11986,radius80,radius80_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_17 (dictionary,horizontal,lo,hi) := (11987,radius81,radius81_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_18 (dictionary,horizontal,lo,hi) := (11988,radius82,radius82_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor1_19 (dictionary,horizontal,lo,hi) := (11989,radius83,radius83_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor1_20 (dictionary,horizontal,lo,hi) := (11990,radius84,radius84_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor1_21 (dictionary,horizontal,lo,hi) := (11991,radius85,radius85_checked,[.single 5, .single 1])
checked_chord_neighbor neighbor1_22 (dictionary,horizontal,lo,hi) := (11992,radius139,radius139_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor1_23 (dictionary,horizontal,lo,hi) := (11993,radius140,radius140_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_24 (dictionary,horizontal,lo,hi) := (11994,radius141,radius141_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_25 (dictionary,horizontal,lo,hi) := (11995,radius151,radius151_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_26 (dictionary,horizontal,lo,hi) := (11996,radius152,radius152_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_27 (dictionary,horizontal,lo,hi) := (11997,radius153,radius153_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_28 (dictionary,horizontal,lo,hi) := (11998,radius154,radius154_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_29 (dictionary,horizontal,lo,hi) := (11999,radius155,radius155_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_30 (dictionary,horizontal,lo,hi) := (12000,radius156,radius156_checked,[.single 6, .single 3])
checked_chord_neighbor neighbor1_31 (dictionary,horizontal,lo,hi) := (12001,radius157,radius157_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_32 (dictionary,horizontal,lo,hi) := (12002,radius158,radius158_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_33 (dictionary,horizontal,lo,hi) := (12003,radius159,radius159_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_34 (dictionary,horizontal,lo,hi) := (12004,radius160,radius160_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_35 (dictionary,horizontal,lo,hi) := (12005,radius161,radius161_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_36 (dictionary,horizontal,lo,hi) := (12006,radius162,radius162_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor1_37 (dictionary,horizontal,lo,hi) := (12007,radius163,radius163_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_38 (dictionary,horizontal,lo,hi) := (12008,radius164,radius164_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_39 (dictionary,horizontal,lo,hi) := (12009,radius165,radius165_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_40 (dictionary,horizontal,lo,hi) := (12010,radius166,radius166_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_41 (dictionary,horizontal,lo,hi) := (12011,radius167,radius167_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_42 (dictionary,horizontal,lo,hi) := (12012,radius168,radius168_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_43 (dictionary,horizontal,lo,hi) := (12013,radius169,radius169_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_44 (dictionary,horizontal,lo,hi) := (12014,radius170,radius170_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_45 (dictionary,horizontal,lo,hi) := (12015,radius171,radius171_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_46 (dictionary,horizontal,lo,hi) := (12016,radius172,radius172_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_47 (dictionary,horizontal,lo,hi) := (12017,radius173,radius173_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_48 (dictionary,horizontal,lo,hi) := (12018,radius174,radius174_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_49 (dictionary,horizontal,lo,hi) := (12019,radius175,radius175_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_50 (dictionary,horizontal,lo,hi) := (12020,radius176,radius176_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_51 (dictionary,horizontal,lo,hi) := (12021,radius177,radius177_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_52 (dictionary,horizontal,lo,hi) := (12022,radius178,radius178_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_53 (dictionary,horizontal,lo,hi) := (12023,radius179,radius179_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_54 (dictionary,horizontal,lo,hi) := (12024,radius180,radius180_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_55 (dictionary,horizontal,lo,hi) := (12025,radius181,radius181_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_56 (dictionary,horizontal,lo,hi) := (12026,radius182,radius182_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_57 (dictionary,horizontal,lo,hi) := (12027,radius183,radius183_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_58 (dictionary,horizontal,lo,hi) := (12028,radius184,radius184_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_59 (dictionary,horizontal,lo,hi) := (12029,radius185,radius185_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_60 (dictionary,horizontal,lo,hi) := (12030,radius186,radius186_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_61 (dictionary,horizontal,lo,hi) := (12031,radius187,radius187_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_62 (dictionary,horizontal,lo,hi) := (12032,radius188,radius188_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_63 (dictionary,horizontal,lo,hi) := (12033,radius189,radius189_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_64 (dictionary,horizontal,lo,hi) := (12034,radius190,radius190_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor1_65 (dictionary,horizontal,lo,hi) := (12035,radius191,radius191_checked,[.single 7, .single 3])
checked_chord_collection neighbors1 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor1_0, neighbor1_1, neighbor1_2, neighbor1_3, neighbor1_4, neighbor1_5, neighbor1_6, neighbor1_7, neighbor1_8, neighbor1_9, neighbor1_10, neighbor1_11,
    neighbor1_12, neighbor1_13, neighbor1_14, neighbor1_15, neighbor1_16, neighbor1_17, neighbor1_18, neighbor1_19, neighbor1_20, neighbor1_21, neighbor1_22, neighbor1_23,
    neighbor1_24, neighbor1_25, neighbor1_26, neighbor1_27, neighbor1_28, neighbor1_29, neighbor1_30, neighbor1_31, neighbor1_32, neighbor1_33, neighbor1_34, neighbor1_35,
    neighbor1_36, neighbor1_37, neighbor1_38, neighbor1_39, neighbor1_40, neighbor1_41, neighbor1_42, neighbor1_43, neighbor1_44, neighbor1_45, neighbor1_46, neighbor1_47,
    neighbor1_48, neighbor1_49, neighbor1_50, neighbor1_51, neighbor1_52, neighbor1_53, neighbor1_54, neighbor1_55, neighbor1_56, neighbor1_57, neighbor1_58, neighbor1_59,
    neighbor1_60, neighbor1_61, neighbor1_62, neighbor1_63, neighbor1_64, neighbor1_65]

theorem neighbors1_sources : neighbors1.map Neighbor.source =
    continuousScout979Domain9_17Ids := by rfl

checked_chord_neighbor neighbor2_0 (dictionary,horizontal,lo,hi) := (9185,radius64,radius64_checked,[.single 6, .single 2])
checked_chord_neighbor neighbor2_1 (dictionary,horizontal,lo,hi) := (9186,radius65,radius65_checked,[.single 5, .single 2])
checked_chord_neighbor neighbor2_2 (dictionary,horizontal,lo,hi) := (9187,radius167,radius167_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_3 (dictionary,horizontal,lo,hi) := (9188,radius168,radius168_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_4 (dictionary,horizontal,lo,hi) := (9189,radius169,radius169_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_5 (dictionary,horizontal,lo,hi) := (9190,radius170,radius170_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_6 (dictionary,horizontal,lo,hi) := (9191,radius171,radius171_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_7 (dictionary,horizontal,lo,hi) := (9192,radius172,radius172_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_8 (dictionary,horizontal,lo,hi) := (9193,radius173,radius173_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_9 (dictionary,horizontal,lo,hi) := (9194,radius174,radius174_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_10 (dictionary,horizontal,lo,hi) := (9195,radius175,radius175_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_11 (dictionary,horizontal,lo,hi) := (9196,radius176,radius176_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_12 (dictionary,horizontal,lo,hi) := (9197,radius177,radius177_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_13 (dictionary,horizontal,lo,hi) := (9198,radius178,radius178_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_14 (dictionary,horizontal,lo,hi) := (9199,radius179,radius179_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_15 (dictionary,horizontal,lo,hi) := (9200,radius180,radius180_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_16 (dictionary,horizontal,lo,hi) := (9201,radius181,radius181_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_17 (dictionary,horizontal,lo,hi) := (9202,radius182,radius182_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_18 (dictionary,horizontal,lo,hi) := (9203,radius183,radius183_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_19 (dictionary,horizontal,lo,hi) := (9204,radius184,radius184_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_20 (dictionary,horizontal,lo,hi) := (9205,radius185,radius185_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_21 (dictionary,horizontal,lo,hi) := (9206,radius186,radius186_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_22 (dictionary,horizontal,lo,hi) := (9207,radius187,radius187_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_23 (dictionary,horizontal,lo,hi) := (9208,radius188,radius188_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_24 (dictionary,horizontal,lo,hi) := (9209,radius189,radius189_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_25 (dictionary,horizontal,lo,hi) := (9210,radius190,radius190_checked,[.single 5, .single 3])
checked_chord_neighbor neighbor2_26 (dictionary,horizontal,lo,hi) := (9211,radius191,radius191_checked,[.single 5, .single 3])
checked_chord_collection neighbors2 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor2_0, neighbor2_1, neighbor2_2, neighbor2_3, neighbor2_4, neighbor2_5, neighbor2_6, neighbor2_7, neighbor2_8, neighbor2_9, neighbor2_10, neighbor2_11,
    neighbor2_12, neighbor2_13, neighbor2_14, neighbor2_15, neighbor2_16, neighbor2_17, neighbor2_18, neighbor2_19, neighbor2_20, neighbor2_21, neighbor2_22, neighbor2_23,
    neighbor2_24, neighbor2_25, neighbor2_26]

theorem neighbors2_sources : neighbors2.map Neighbor.source =
    continuousScout979Domain11_19Ids := by rfl

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (11805,radius64,radius64_checked,chord_keep%(11834,[.single 1, .single 2, .pair 1 3, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 8, .single 0, .single 2, .pair 0 7, .copy 13]),chord_close%(⟨[0,4],[(4,0),(5,4)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (11806,radius65,radius65_checked,chord_keep%(11835,[.single 1, .single 2, .pair 1 3, .single 0, .pair 0 7, .pair 1 7, .single 8, .single 8, .single 0, .single 2, .pair 0 7, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (11807,radius66,radius66_checked,chord_keep%(11836,[.single 1, .single 2, .pair 1 3, .single 0, .pair 0 8, .pair 1 8, .single 9, .single 9, .single 0, .single 2, .pair 0 8, .copy 14]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (11808,radius67,radius67_checked,chord_close%(⟨[0,8],[(2,0),(25,8)]⟩),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (11809,radius167,radius167_checked,chord_keep%(11837,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (11810,radius168,radius168_checked,chord_keep%(11838,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(8,0),(1,4)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (11811,radius169,radius169_checked,chord_keep%(11839,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (11812,radius170,radius170_checked,chord_keep%(11840,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (11813,radius171,radius171_checked,chord_keep%(11841,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (11814,radius172,radius172_checked,chord_keep%(11842,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (11815,radius173,radius173_checked,chord_keep%(11843,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (11816,radius174,radius174_checked,chord_keep%(11844,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (11817,radius175,radius175_checked,chord_keep%(11845,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(50,0),(1,4)]⟩))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (11818,radius176,radius176_checked,chord_keep%(11846,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(32,0),(5,4)]⟩))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (11819,radius177,radius177_checked,chord_keep%(11847,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (11820,radius178,radius178_checked,chord_keep%(11848,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (11821,radius179,radius179_checked,chord_keep%(11849,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(5,0),(4,4)]⟩))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (11822,radius180,radius180_checked,chord_keep%(11850,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(5,0),(2,4)]⟩))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (11823,radius181,radius181_checked,chord_keep%(11851,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (11824,radius182,radius182_checked,chord_keep%(11852,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(40,0),(1,4)]⟩))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (11825,radius183,radius183_checked,chord_keep%(11853,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (11826,radius184,radius184_checked,chord_keep%(11854,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (11827,radius185,radius185_checked,chord_keep%(11855,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (11828,radius186,radius186_checked,chord_keep%(11856,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (11829,radius187,radius187_checked,chord_keep%(11857,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (11830,radius188,radius188_checked,chord_keep%(11858,[.single 1, .single 2, .pair 1 3, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .single 2, .single 6, .copy 13]),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (11831,radius189,radius189_checked,chord_keep%(11859,[.single 1, .single 2, .pair 1 3, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .single 0, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(10,5)]⟩))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (11832,radius190,radius190_checked,chord_keep%(11860,[.single 1, .single 2, .pair 1 3, .single 0, .pair 6 7, .single 7, .single 8, .single 9, .single 9, .single 0, .single 2, .single 7, .copy 14]),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (11833,radius191,radius191_checked,chord_keep%(11861,[.pair 1 6, .pair 0 1, .single 0, .pair 5 6, .single 6, .single 7, .single 8, .single 8, .single 0, .pair 0 1, .single 6, .copy 13]),chord_close%(⟨[0,4],[(1,0),(5,4)]⟩))
checked_chord_collection plans : (IndexedChord.Plan dictionary horizontal lo hi) =>
  (fun (entry : IndexedChord.Plan dictionary horizontal lo hi) => entry.Check) := [
    plan0, plan1, plan2, plan3, plan4, plan5, plan6, plan7, plan8, plan9, plan10, plan11,
    plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23,
    plan24, plan25, plan26, plan27, plan28]

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout979Domain7_16Ids := by rfl
def outputIds : List (Fin poseCount) := [11834,11835,11836,11837,11838,11839,11840,11841,11842,11843,11844,11845,11846,11847,11848,11849,11850,11851,11852,11853,11854,11855,11856,11857,11858,11859,11860,11861]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout979Domain7_25Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout979Domain7_25Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout979Domain7_16 (q 0))
    (h0 : OrientedPoseCovered continuousScout979Domain6_24 (q 1))
    (h1 : OrientedPoseCovered continuousScout979Domain9_17 (q 2))
    (h2 : OrientedPoseCovered continuousScout979Domain11_19 (q 3))
    : OrientedPoseCovered continuousScout979Domain7_25 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout979Domain7_16Ids continuousScout979Domain7_25Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain6_24Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain9_17Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain11_19Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![3072,512,8192,32768]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout979Domain7_16 (p.square (ownerIndex p 3072)))
    (h0 : OrientedPoseCovered continuousScout979Domain6_24 (p.square (ownerIndex p 512)))
    (h1 : OrientedPoseCovered continuousScout979Domain9_17 (p.square (ownerIndex p 8192)))
    (h2 : OrientedPoseCovered continuousScout979Domain11_19 (p.square (ownerIndex p 32768)))
    : OrientedPoseCovered continuousScout979Domain7_25 (p.square (ownerIndex p 3072)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout979Domain7_16 continuousScout979Domain7_25
    ![continuousScout979Domain6_24,continuousScout979Domain9_17,continuousScout979Domain11_19]
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
end N12Compact.Preservation.Chords.C979Step24

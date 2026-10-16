import Compact.Bridge.ChordSyntax
import Compact.Bridge.ChordPacking
import Compact.Preservation.Chords.Radii
import Compact.Preservation.C979

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.C979Step21
open S12 S12Pilot IntegerSupport IndexedChord DirectPruningPlan
open N12Compact.Preservation.HistoricalBank
noncomputable section

open N12Compact.Preservation.C979

open N12Compact.Preservation.Chords.Radii
def horizontal : Bool := false
def lo : ℚ := (224837169/100000000)
def hi : ℚ := (112943613/50000000)
theorem ordered : lo ≤ hi := by norm_num [lo,hi]

checked_chord_neighbor neighbor0_0 (dictionary,horizontal,lo,hi) := (11805,radius64,radius64_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_1 (dictionary,horizontal,lo,hi) := (11806,radius65,radius65_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_2 (dictionary,horizontal,lo,hi) := (11807,radius66,radius66_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor0_3 (dictionary,horizontal,lo,hi) := (11808,radius67,radius67_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_4 (dictionary,horizontal,lo,hi) := (11809,radius167,radius167_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_5 (dictionary,horizontal,lo,hi) := (11810,radius168,radius168_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_6 (dictionary,horizontal,lo,hi) := (11811,radius169,radius169_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_7 (dictionary,horizontal,lo,hi) := (11812,radius170,radius170_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_8 (dictionary,horizontal,lo,hi) := (11813,radius171,radius171_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_9 (dictionary,horizontal,lo,hi) := (11814,radius172,radius172_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_10 (dictionary,horizontal,lo,hi) := (11815,radius173,radius173_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_11 (dictionary,horizontal,lo,hi) := (11816,radius174,radius174_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_12 (dictionary,horizontal,lo,hi) := (11817,radius175,radius175_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_13 (dictionary,horizontal,lo,hi) := (11818,radius176,radius176_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_14 (dictionary,horizontal,lo,hi) := (11819,radius177,radius177_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_15 (dictionary,horizontal,lo,hi) := (11820,radius178,radius178_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_16 (dictionary,horizontal,lo,hi) := (11821,radius179,radius179_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_17 (dictionary,horizontal,lo,hi) := (11822,radius180,radius180_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_18 (dictionary,horizontal,lo,hi) := (11823,radius181,radius181_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_19 (dictionary,horizontal,lo,hi) := (11824,radius182,radius182_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_20 (dictionary,horizontal,lo,hi) := (11825,radius183,radius183_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_21 (dictionary,horizontal,lo,hi) := (11826,radius184,radius184_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_22 (dictionary,horizontal,lo,hi) := (11827,radius185,radius185_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_23 (dictionary,horizontal,lo,hi) := (11828,radius186,radius186_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_24 (dictionary,horizontal,lo,hi) := (11829,radius187,radius187_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_25 (dictionary,horizontal,lo,hi) := (11830,radius188,radius188_checked,[.single 7, .single 3])
checked_chord_neighbor neighbor0_26 (dictionary,horizontal,lo,hi) := (11831,radius189,radius189_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor0_27 (dictionary,horizontal,lo,hi) := (11832,radius190,radius190_checked,[.single 8, .single 4])
checked_chord_neighbor neighbor0_28 (dictionary,horizontal,lo,hi) := (11833,radius191,radius191_checked,[.single 7, .single 3])
checked_chord_collection neighbors0 : (Neighbor dictionary) =>
  (fun (entry : Neighbor dictionary) => entry.Check horizontal lo hi) := [
    neighbor0_0, neighbor0_1, neighbor0_2, neighbor0_3, neighbor0_4, neighbor0_5, neighbor0_6, neighbor0_7, neighbor0_8, neighbor0_9, neighbor0_10, neighbor0_11,
    neighbor0_12, neighbor0_13, neighbor0_14, neighbor0_15, neighbor0_16, neighbor0_17, neighbor0_18, neighbor0_19, neighbor0_20, neighbor0_21, neighbor0_22, neighbor0_23,
    neighbor0_24, neighbor0_25, neighbor0_26, neighbor0_27, neighbor0_28]

theorem neighbors0_sources : neighbors0.map Neighbor.source =
    continuousScout979Domain7_16Ids := by rfl

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

checked_chord_plan plan0 (dictionary,horizontal,lo,hi) := (11244,radius64,radius64_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan1 (dictionary,horizontal,lo,hi) := (11245,radius65,radius65_checked,chord_close%(⟨[0,8],[(1,0),(8,8)]⟩),chord_close%(⟨[0,4],[(2,0),(1,4)]⟩))
checked_chord_plan plan2 (dictionary,horizontal,lo,hi) := (11246,radius66,radius66_checked,chord_close%(⟨[0,9],[(1,0),(20,9)]⟩),chord_close%(⟨[0,5],[(5,0),(1,5)]⟩))
checked_chord_plan plan3 (dictionary,horizontal,lo,hi) := (11247,radius67,radius67_checked,chord_close%(⟨[0,9],[(1,0),(5,9)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan4 (dictionary,horizontal,lo,hi) := (11248,radius68,radius68_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(4,4)]⟩))
checked_chord_plan plan5 (dictionary,horizontal,lo,hi) := (11249,radius69,radius69_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_close%(⟨[0,4],[(32,0),(1,4)]⟩))
checked_chord_plan plan6 (dictionary,horizontal,lo,hi) := (11250,radius70,radius70_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(2,4)]⟩))
checked_chord_plan plan7 (dictionary,horizontal,lo,hi) := (11251,radius71,radius71_checked,chord_close%(⟨[0,8],[(2,0),(5,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan8 (dictionary,horizontal,lo,hi) := (11252,radius72,radius72_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan9 (dictionary,horizontal,lo,hi) := (11253,radius73,radius73_checked,chord_close%(⟨[0,9],[(16,0),(1,9)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan10 (dictionary,horizontal,lo,hi) := (11254,radius74,radius74_checked,chord_close%(⟨[0,9],[(1,0),(10,9)]⟩),chord_close%(⟨[0,5],[(1,0),(2,5)]⟩))
checked_chord_plan plan11 (dictionary,horizontal,lo,hi) := (11255,radius75,radius75_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_close%(⟨[0,5],[(64,0),(5,5)]⟩))
checked_chord_plan plan12 (dictionary,horizontal,lo,hi) := (11256,radius76,radius76_checked,chord_close%(⟨[0,9],[(1,0),(25,9)]⟩),chord_keep%(11367,[.pair 0 3, .pair 3 4, .single 4, .pair 2 5, .pair 0 5, .single 0, .single 0, .single 4, .pair 0 3, .pair 0 5, .copy 14]))
checked_chord_plan plan13 (dictionary,horizontal,lo,hi) := (11257,radius77,radius77_checked,chord_close%(⟨[0,9],[(4,0),(25,9)]⟩),chord_keep%(11368,[.pair 0 3, .pair 3 4, .single 4, .single 5, .pair 2 6, .pair 0 6, .single 0, .single 0, .single 4, .pair 0 3, .pair 0 6, .copy 14]))
checked_chord_plan plan14 (dictionary,horizontal,lo,hi) := (11258,radius78,radius78_checked,chord_close%(⟨[0,9],[(1,0),(10,9)]⟩),chord_keep%(11369,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .single 0, .single 0, .single 4, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan15 (dictionary,horizontal,lo,hi) := (11259,radius79,radius79_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(11370,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .single 0, .single 0, .single 4, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan16 (dictionary,horizontal,lo,hi) := (11260,radius80,radius80_checked,chord_close%(⟨[0,9],[(25,0),(1,9)]⟩),chord_keep%(11371,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .single 0, .single 0, .single 4, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan17 (dictionary,horizontal,lo,hi) := (11261,radius81,radius81_checked,chord_close%(⟨[0,9],[(1,0),(5,9)]⟩),chord_keep%(11372,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .single 0, .single 0, .single 4, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan18 (dictionary,horizontal,lo,hi) := (11262,radius82,radius82_checked,chord_close%(⟨[0,9],[(25,0),(1,9)]⟩),chord_keep%(11373,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .single 0, .single 0, .single 4, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan19 (dictionary,horizontal,lo,hi) := (11263,radius83,radius83_checked,chord_close%(⟨[0,9],[(2,0),(1,9)]⟩),chord_keep%(11374,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 4 8, .single 0, .single 0, .single 4, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan20 (dictionary,horizontal,lo,hi) := (11264,radius84,radius84_checked,chord_close%(⟨[0,10],[(4,0),(1,10)]⟩),chord_keep%(11375,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .single 8, .pair 5 9, .single 0, .single 0, .single 5, .pair 0 4, .single 8, .copy 15]))
checked_chord_plan plan21 (dictionary,horizontal,lo,hi) := (11265,radius85,radius85_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(11376,[.pair 0 4, .pair 4 5, .single 5, .single 6, .single 7, .pair 5 8, .single 0, .single 0, .single 5, .pair 0 4, .single 7, .copy 14]))
checked_chord_plan plan22 (dictionary,horizontal,lo,hi) := (11266,radius86,radius86_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(11377,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .single 7, .pair 5 8, .single 0, .single 0, .single 5, .pair 0 3, .single 7, .copy 14]))
checked_chord_plan plan23 (dictionary,horizontal,lo,hi) := (11267,radius87,radius87_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11378,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan24 (dictionary,horizontal,lo,hi) := (11268,radius88,radius88_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11379,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 4 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan25 (dictionary,horizontal,lo,hi) := (11269,radius89,radius89_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11380,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan26 (dictionary,horizontal,lo,hi) := (11270,radius90,radius90_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11381,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan27 (dictionary,horizontal,lo,hi) := (11271,radius91,radius91_checked,chord_close%(⟨[0,8],[(1,0),(5,8)]⟩),chord_keep%(11382,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan28 (dictionary,horizontal,lo,hi) := (11272,radius92,radius92_checked,chord_close%(⟨[0,8],[(1,0),(4,8)]⟩),chord_keep%(11383,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan29 (dictionary,horizontal,lo,hi) := (11273,radius93,radius93_checked,chord_close%(⟨[0,8],[(10,0),(1,8)]⟩),chord_keep%(11384,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan30 (dictionary,horizontal,lo,hi) := (11274,radius94,radius94_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11385,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan31 (dictionary,horizontal,lo,hi) := (11275,radius95,radius95_checked,chord_close%(⟨[0,8],[(2,0),(5,8)]⟩),chord_keep%(11386,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan32 (dictionary,horizontal,lo,hi) := (11276,radius96,radius96_checked,chord_close%(⟨[0,8],[(1,0),(4,8)]⟩),chord_keep%(11387,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan33 (dictionary,horizontal,lo,hi) := (11277,radius97,radius97_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11388,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan34 (dictionary,horizontal,lo,hi) := (11278,radius98,radius98_checked,chord_close%(⟨[0,8],[(320,0),(1,8)]⟩),chord_keep%(11389,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan35 (dictionary,horizontal,lo,hi) := (11279,radius99,radius99_checked,chord_close%(⟨[0,8],[(1,0),(20,8)]⟩),chord_keep%(11390,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan36 (dictionary,horizontal,lo,hi) := (11280,radius100,radius100_checked,chord_close%(⟨[0,8],[(8,0),(1,8)]⟩),chord_keep%(11391,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan37 (dictionary,horizontal,lo,hi) := (11281,radius101,radius101_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11392,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan38 (dictionary,horizontal,lo,hi) := (11282,radius102,radius102_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_keep%(11393,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan39 (dictionary,horizontal,lo,hi) := (11283,radius103,radius103_checked,chord_close%(⟨[0,7],[(2,0),(5,7)]⟩),chord_keep%(11394,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan40 (dictionary,horizontal,lo,hi) := (11284,radius104,radius104_checked,chord_close%(⟨[0,7],[(1,0),(20,7)]⟩),chord_keep%(11395,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan41 (dictionary,horizontal,lo,hi) := (11285,radius105,radius105_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11396,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan42 (dictionary,horizontal,lo,hi) := (11286,radius106,radius106_checked,chord_close%(⟨[0,7],[(1,0),(20,7)]⟩),chord_keep%(11397,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan43 (dictionary,horizontal,lo,hi) := (11287,radius107,radius107_checked,chord_close%(⟨[0,7],[(5,0),(1,7)]⟩),chord_keep%(11398,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan44 (dictionary,horizontal,lo,hi) := (11288,radius108,radius108_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(11399,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan45 (dictionary,horizontal,lo,hi) := (11289,radius109,radius109_checked,chord_close%(⟨[0,7],[(1,0),(100,7)]⟩),chord_keep%(11400,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan46 (dictionary,horizontal,lo,hi) := (11290,radius110,radius110_checked,chord_close%(⟨[0,7],[(8,0),(1,7)]⟩),chord_keep%(11401,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 1, .single 5, .copy 12]))
checked_chord_plan plan47 (dictionary,horizontal,lo,hi) := (11291,radius114,radius114_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11402,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan48 (dictionary,horizontal,lo,hi) := (11292,radius115,radius115_checked,chord_close%(⟨[0,7],[(1,0),(125,7)]⟩),chord_keep%(11403,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan49 (dictionary,horizontal,lo,hi) := (11293,radius116,radius116_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(11404,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan50 (dictionary,horizontal,lo,hi) := (11294,radius117,radius117_checked,chord_close%(⟨[0,7],[(1,0),(25,7)]⟩),chord_keep%(11405,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan51 (dictionary,horizontal,lo,hi) := (11295,radius118,radius118_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(11406,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan52 (dictionary,horizontal,lo,hi) := (11296,radius119,radius119_checked,chord_close%(⟨[0,7],[(1,0),(10,7)]⟩),chord_keep%(11407,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan53 (dictionary,horizontal,lo,hi) := (11297,radius120,radius120_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11408,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan54 (dictionary,horizontal,lo,hi) := (11298,radius121,radius121_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11409,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan55 (dictionary,horizontal,lo,hi) := (11299,radius122,radius122_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11410,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan56 (dictionary,horizontal,lo,hi) := (11300,radius123,radius123_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11411,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan57 (dictionary,horizontal,lo,hi) := (11301,radius124,radius124_checked,chord_close%(⟨[0,7],[(4,0),(1,7)]⟩),chord_keep%(11412,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan58 (dictionary,horizontal,lo,hi) := (11302,radius125,radius125_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_keep%(11413,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan59 (dictionary,horizontal,lo,hi) := (11303,radius126,radius126_checked,chord_close%(⟨[0,7],[(1,0),(16,7)]⟩),chord_keep%(11414,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan60 (dictionary,horizontal,lo,hi) := (11304,radius127,radius127_checked,chord_close%(⟨[0,7],[(16,0),(1,7)]⟩),chord_keep%(11415,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan61 (dictionary,horizontal,lo,hi) := (11305,radius128,radius128_checked,chord_close%(⟨[0,7],[(1,0),(10,7)]⟩),chord_keep%(11416,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan62 (dictionary,horizontal,lo,hi) := (11306,radius129,radius129_checked,chord_close%(⟨[0,7],[(5,0),(2,7)]⟩),chord_keep%(11417,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan63 (dictionary,horizontal,lo,hi) := (11307,radius130,radius130_checked,chord_close%(⟨[0,7],[(5,0),(2,7)]⟩),chord_keep%(11418,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan64 (dictionary,horizontal,lo,hi) := (11308,radius131,radius131_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_keep%(11419,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan65 (dictionary,horizontal,lo,hi) := (11309,radius132,radius132_checked,chord_close%(⟨[0,7],[(1,0),(10,7)]⟩),chord_keep%(11420,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan66 (dictionary,horizontal,lo,hi) := (11310,radius133,radius133_checked,chord_close%(⟨[0,7],[(1,0),(8,7)]⟩),chord_keep%(11421,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan67 (dictionary,horizontal,lo,hi) := (11311,radius134,radius134_checked,chord_close%(⟨[0,7],[(10,0),(1,7)]⟩),chord_keep%(11422,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan68 (dictionary,horizontal,lo,hi) := (11312,radius135,radius135_checked,chord_close%(⟨[0,7],[(1,0),(64,7)]⟩),chord_keep%(11423,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan69 (dictionary,horizontal,lo,hi) := (11313,radius136,radius136_checked,chord_close%(⟨[0,7],[(1,0),(16,7)]⟩),chord_keep%(11424,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan70 (dictionary,horizontal,lo,hi) := (11314,radius137,radius137_checked,chord_close%(⟨[0,7],[(5,0),(1,7)]⟩),chord_keep%(11425,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan71 (dictionary,horizontal,lo,hi) := (11315,radius138,radius138_checked,chord_close%(⟨[0,7],[(1,0),(4,7)]⟩),chord_keep%(11426,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 7, .single 3, .single 2, .single 5, .copy 12]))
checked_chord_plan plan72 (dictionary,horizontal,lo,hi) := (11316,radius139,radius139_checked,chord_close%(⟨[0,8],[(8,0),(1,8)]⟩),chord_keep%(11427,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan73 (dictionary,horizontal,lo,hi) := (11317,radius140,radius140_checked,chord_close%(⟨[0,8],[(1,0),(20,8)]⟩),chord_keep%(11428,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan74 (dictionary,horizontal,lo,hi) := (11318,radius141,radius141_checked,chord_close%(⟨[0,8],[(1,0),(32,8)]⟩),chord_keep%(11429,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan75 (dictionary,horizontal,lo,hi) := (11319,radius142,radius142_checked,chord_close%(⟨[0,8],[(1,0),(5,8)]⟩),chord_keep%(11430,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan76 (dictionary,horizontal,lo,hi) := (11320,radius143,radius143_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_keep%(11431,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan77 (dictionary,horizontal,lo,hi) := (11321,radius144,radius144_checked,chord_close%(⟨[0,9],[(1,0),(10,9)]⟩),chord_keep%(11432,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 9, .single 9, .single 4, .single 2, .single 7, .copy 14]))
checked_chord_plan plan78 (dictionary,horizontal,lo,hi) := (11322,radius145,radius145_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11433,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan79 (dictionary,horizontal,lo,hi) := (11323,radius146,radius146_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11434,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan80 (dictionary,horizontal,lo,hi) := (11324,radius147,radius147_checked,chord_close%(⟨[0,8],[(1,0),(8,8)]⟩),chord_keep%(11435,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan81 (dictionary,horizontal,lo,hi) := (11325,radius148,radius148_checked,chord_close%(⟨[0,8],[(16,0),(25,8)]⟩),chord_keep%(11436,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan82 (dictionary,horizontal,lo,hi) := (11326,radius149,radius149_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11437,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan83 (dictionary,horizontal,lo,hi) := (11327,radius150,radius150_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11438,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan84 (dictionary,horizontal,lo,hi) := (11328,radius151,radius151_checked,chord_close%(⟨[0,8],[(5,0),(1,8)]⟩),chord_keep%(11439,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan85 (dictionary,horizontal,lo,hi) := (11329,radius152,radius152_checked,chord_close%(⟨[0,8],[(25,0),(1,8)]⟩),chord_keep%(11440,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan86 (dictionary,horizontal,lo,hi) := (11330,radius153,radius153_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11441,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan87 (dictionary,horizontal,lo,hi) := (11331,radius154,radius154_checked,chord_close%(⟨[0,8],[(1,0),(2,8)]⟩),chord_keep%(11442,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan88 (dictionary,horizontal,lo,hi) := (11332,radius155,radius155_checked,chord_close%(⟨[0,8],[(5,0),(32,8)]⟩),chord_keep%(11443,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan89 (dictionary,horizontal,lo,hi) := (11333,radius156,radius156_checked,chord_close%(⟨[0,8],[(1,0),(2,8)]⟩),chord_keep%(11444,[.single 1, .single 2, .single 3, .single 4, .single 5, .single 6, .single 7, .single 8, .single 8, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan90 (dictionary,horizontal,lo,hi) := (11334,radius157,radius157_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11445,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan91 (dictionary,horizontal,lo,hi) := (11335,radius158,radius158_checked,chord_close%(⟨[0,8],[(16,0),(1,8)]⟩),chord_keep%(11446,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan92 (dictionary,horizontal,lo,hi) := (11336,radius159,radius159_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11447,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan93 (dictionary,horizontal,lo,hi) := (11337,radius160,radius160_checked,chord_close%(⟨[0,8],[(1,0),(4,8)]⟩),chord_keep%(11448,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan94 (dictionary,horizontal,lo,hi) := (11338,radius161,radius161_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11449,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan95 (dictionary,horizontal,lo,hi) := (11339,radius162,radius162_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11450,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan96 (dictionary,horizontal,lo,hi) := (11340,radius163,radius163_checked,chord_close%(⟨[0,8],[(4,0),(5,8)]⟩),chord_keep%(11451,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan97 (dictionary,horizontal,lo,hi) := (11341,radius164,radius164_checked,chord_close%(⟨[0,7],[(2,0),(25,7)]⟩),chord_keep%(11452,[.pair 0 3, .pair 3 4, .single 4, .single 5, .pair 3 6, .single 0, .single 0, .single 4, .pair 0 3, .single 5, .copy 12]))
checked_chord_plan plan98 (dictionary,horizontal,lo,hi) := (11342,radius167,radius167_checked,chord_close%(⟨[0,8],[(25,0),(2,8)]⟩),chord_keep%(11453,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan99 (dictionary,horizontal,lo,hi) := (11343,radius168,radius168_checked,chord_close%(⟨[0,8],[(128,0),(1,8)]⟩),chord_keep%(11454,[.pair 1 2, .single 2, .single 3, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .single 2, .single 6, .copy 13]))
checked_chord_plan plan100 (dictionary,horizontal,lo,hi) := (11344,radius169,radius169_checked,chord_close%(⟨[0,8],[(1,0),(10,8)]⟩),chord_keep%(11455,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .pair 0 3, .single 6, .copy 13]))
checked_chord_plan plan101 (dictionary,horizontal,lo,hi) := (11345,radius170,radius170_checked,chord_close%(⟨[0,8],[(1,0),(80,8)]⟩),chord_keep%(11456,[.pair 0 3, .pair 3 4, .single 4, .single 5, .single 6, .pair 3 7, .single 0, .single 0, .single 4, .pair 0 3, .single 6, .copy 13]))
checked_chord_plan plan102 (dictionary,horizontal,lo,hi) := (11346,radius171,radius171_checked,chord_close%(⟨[0,8],[(5,0),(1,8)]⟩),chord_keep%(11457,[.pair 0 3, .pair 3 4, .single 4, .pair 1 5, .pair 0 5, .single 0, .single 0, .single 4, .pair 0 3, .pair 0 5, .copy 13]))
checked_chord_plan plan103 (dictionary,horizontal,lo,hi) := (11347,radius172,radius172_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_keep%(11458,[.pair 0 3, .pair 3 4, .single 4, .pair 1 5, .pair 0 5, .single 0, .single 0, .single 4, .pair 0 3, .pair 0 5, .copy 13]))
checked_chord_plan plan104 (dictionary,horizontal,lo,hi) := (11348,radius173,radius173_checked,chord_close%(⟨[0,8],[(5,0),(1,8)]⟩),chord_close%(⟨[0,4],[(5,0),(1,4)]⟩))
checked_chord_plan plan105 (dictionary,horizontal,lo,hi) := (11349,radius174,radius174_checked,chord_close%(⟨[0,8],[(4,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan106 (dictionary,horizontal,lo,hi) := (11350,radius175,radius175_checked,chord_close%(⟨[0,9],[(1,0),(1,9)]⟩),chord_close%(⟨[0,5],[(1,0),(5,5)]⟩))
checked_chord_plan plan107 (dictionary,horizontal,lo,hi) := (11351,radius176,radius176_checked,chord_close%(⟨[0,9],[(16,0),(1,9)]⟩),chord_close%(⟨[0,5],[(1,0),(1,5)]⟩))
checked_chord_plan plan108 (dictionary,horizontal,lo,hi) := (11352,radius177,radius177_checked,chord_close%(⟨[0,9],[(5,0),(4,9)]⟩),chord_close%(⟨[0,5],[(5,0),(1,5)]⟩))
checked_chord_plan plan109 (dictionary,horizontal,lo,hi) := (11353,radius178,radius178_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_close%(⟨[0,5],[(8,0),(1,5)]⟩))
checked_chord_plan plan110 (dictionary,horizontal,lo,hi) := (11354,radius179,radius179_checked,chord_close%(⟨[0,10],[(2,0),(1,10)]⟩),chord_close%(⟨[0,5],[(1,0),(25,5)]⟩))
checked_chord_plan plan111 (dictionary,horizontal,lo,hi) := (11355,radius180,radius180_checked,chord_close%(⟨[0,10],[(1,0),(1,10)]⟩),chord_close%(⟨[0,5],[(1,0),(5,5)]⟩))
checked_chord_plan plan112 (dictionary,horizontal,lo,hi) := (11356,radius181,radius181_checked,chord_close%(⟨[0,7],[(1,0),(5,7)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan113 (dictionary,horizontal,lo,hi) := (11357,radius182,radius182_checked,chord_close%(⟨[0,7],[(8,0),(1,7)]⟩),chord_close%(⟨[0,3],[(1,0),(5,3)]⟩))
checked_chord_plan plan114 (dictionary,horizontal,lo,hi) := (11358,radius183,radius183_checked,chord_close%(⟨[0,7],[(1,0),(2,7)]⟩),chord_close%(⟨[0,3],[(80,0),(1,3)]⟩))
checked_chord_plan plan115 (dictionary,horizontal,lo,hi) := (11359,radius184,radius184_checked,chord_close%(⟨[0,7],[(2,0),(125,7)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan116 (dictionary,horizontal,lo,hi) := (11360,radius185,radius185_checked,chord_close%(⟨[0,7],[(10,0),(1,7)]⟩),chord_close%(⟨[0,3],[(5,0),(1,3)]⟩))
checked_chord_plan plan117 (dictionary,horizontal,lo,hi) := (11361,radius186,radius186_checked,chord_close%(⟨[0,7],[(8,0),(1,7)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan118 (dictionary,horizontal,lo,hi) := (11362,radius187,radius187_checked,chord_close%(⟨[0,7],[(2,0),(1,7)]⟩),chord_close%(⟨[0,3],[(1,0),(1,3)]⟩))
checked_chord_plan plan119 (dictionary,horizontal,lo,hi) := (11363,radius188,radius188_checked,chord_close%(⟨[0,7],[(1,0),(1,7)]⟩),chord_close%(⟨[0,3],[(1,0),(25,3)]⟩))
checked_chord_plan plan120 (dictionary,horizontal,lo,hi) := (11364,radius189,radius189_checked,chord_close%(⟨[0,7],[(5,0),(1,7)]⟩),chord_close%(⟨[0,3],[(5,0),(1,3)]⟩))
checked_chord_plan plan121 (dictionary,horizontal,lo,hi) := (11365,radius190,radius190_checked,chord_close%(⟨[0,8],[(1,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
checked_chord_plan plan122 (dictionary,horizontal,lo,hi) := (11366,radius191,radius191_checked,chord_close%(⟨[0,8],[(2,0),(1,8)]⟩),chord_close%(⟨[0,4],[(1,0),(1,4)]⟩))
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

theorem plans_sources : plans.map IndexedChord.Plan.source = continuousScout979Domain6_21Ids := by rfl
def outputIds : List (Fin poseCount) := [11367,11368,11369,11370,11371,11372,11373,11374,11375,11376,11377,11378,11379,11380,11381,11382,11383,11384,11385,11386,11387,11388,11389,11390,11391,11392,11393,11394,11395,11396,11397,11398,11399,11400,11401,11402,11403,11404,11405,11406,11407,11408,11409,11410,11411,11412,11413,11414,11415,11416,11417,11418,11419,11420,11421,11422,11423,11424,11425,11426,11427,11428,11429,11430,11431,11432,11433,11434,11435,11436,11437,11438,11439,11440,11441,11442,11443,11444,11445,11446,11447,11448,11449,11450,11451,11452,11453,11454,11455,11456,11457,11458]
theorem outputs_exact : plans.flatMap IndexedChord.Plan.targets = outputIds := by rfl
theorem outputs_mem : outputIds.all (fun i => decide (i ∈ continuousScout979Domain6_22Ids)) = true := by
  decide +kernel
theorem outputs_included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ continuousScout979Domain6_22Ids := by
  intro plan member target included
  have hm : target ∈ outputIds := by
    rw [← outputs_exact]
    exact List.mem_flatMap.mpr ⟨plan,member,included⟩
  exact of_decide_eq_true (List.all_eq_true.mp outputs_mem target hm)

theorem sound (q : Fin 4 → OpenSquare)
    (side : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered continuousScout979Domain6_21 (q 0))
    (h0 : OrientedPoseCovered continuousScout979Domain7_16 (q 1))
    (h1 : OrientedPoseCovered continuousScout979Domain9_17 (q 2))
    (h2 : OrientedPoseCovered continuousScout979Domain11_19 (q 3))
    : OrientedPoseCovered continuousScout979Domain6_22 (q 0) := by
  apply IndexedChord.plans_cover dictionary horizontal lo hi ordered positive_denominators
    continuousScout979Domain6_21Ids continuousScout979Domain6_22Ids plans
    plans_sources outputs_included plans_checked q side box disjoint incoming
  intro cut low high i
  fin_cases i
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain7_16Ids neighbors0 neighbors0_sources neighbors0_checked
      (q 1) (side 1) h0 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain9_17Ids neighbors1 neighbors1_sources neighbors1_checked
      (q 2) (side 2) h1 cut low high
  · exact IndexedChord.neighbor_cover dictionary horizontal lo hi positive_denominators
      continuousScout979Domain11_19Ids neighbors2 neighbors2_sources neighbors2_checked
      (q 3) (side 3) h2 cut low high

def masks : Fin 4 → Nat := ![512,3072,8192,32768]
theorem masks_members : ∀ i, masks i ∈ family := by decide +kernel
theorem masks_distinct : Function.Injective masks := by decide +kernel
theorem packing_sound (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered continuousScout979Domain6_21 (p.square (ownerIndex p 512)))
    (h0 : OrientedPoseCovered continuousScout979Domain7_16 (p.square (ownerIndex p 3072)))
    (h1 : OrientedPoseCovered continuousScout979Domain9_17 (p.square (ownerIndex p 8192)))
    (h2 : OrientedPoseCovered continuousScout979Domain11_19 (p.square (ownerIndex p 32768)))
    : OrientedPoseCovered continuousScout979Domain6_22 (p.square (ownerIndex p 512)) := by
  apply ChordPacking.transfer family masks masks_members masks_distinct continuousScout979Domain6_21 continuousScout979Domain6_22
    ![continuousScout979Domain7_16,continuousScout979Domain9_17,continuousScout979Domain11_19]
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
end N12Compact.Preservation.Chords.C979Step21

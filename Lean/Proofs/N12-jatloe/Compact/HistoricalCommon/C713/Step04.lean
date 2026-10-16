import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step04
import Compact.HistoricalCommon.C713.Step04Groups00
import Compact.HistoricalCommon.C713.Step04Groups01
import Compact.HistoricalCommon.C713.Step04Groups02
import Compact.HistoricalCommon.C713.Step04Groups03
import Compact.HistoricalCommon.C713.Step04Groups04
import Compact.HistoricalCommon.C713.Step04Groups05
import Compact.HistoricalCommon.C713.Step04Groups06
import Compact.HistoricalCommon.C713.Step04Groups07

namespace N12Compact.HistoricalCommon.C713.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 27 (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 28 .leaf (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 13 .leaf .leaf) .leaf)))))) (.sourceCut 27 (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.neighborCut 7 (.sourceCut 13 .leaf .leaf) (.neighborCut 28 (.sourceCut 13 .leaf .leaf) .leaf))))))) (.neighborCut 7 (.sourceCut 27 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 28 .leaf (.sourceCut 27 (.neighborCut 14 (.sourceCut 13 .leaf .leaf) (.neighborCut 14 .leaf .leaf)) (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 14 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,109,0,113⟩ scopes := by decide +kernel

theorem covered (i : Fin 109) (j : Fin 113) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 109) (j : Fin 113) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context2925_header,context2936_header,context2947_header,context2958_header,context2969_header,context2980_header,context2991_header,context3002_header,context3013_header,context2915_header,context2916_header,context2917_header,context2918_header,context2919_header,context2920_header,context2921_header,context2922_header,context2923_header,context2924_header,context2926_header,context2927_header,context2928_header,context2929_header,context2930_header,context2931_header,context2932_header,context2933_header,context2934_header,context2935_header,context2937_header,context2938_header,context2939_header,context2940_header,context2941_header,context2942_header,context2943_header,context2944_header,context2945_header,context2946_header,context2948_header,context2949_header,context2950_header,context2951_header,context2952_header,context2953_header,context2954_header,context2955_header,context2956_header,context2957_header,context2959_header,context2960_header,context2961_header,context2962_header,context2963_header,context2964_header,context2965_header,context2966_header,context2967_header,context2968_header,context2970_header,context2971_header,context2972_header,context2973_header,context2974_header,context2975_header,context2976_header,context2977_header,context2978_header,context2979_header,context2981_header,context2982_header,context2983_header,context2984_header,context2985_header,context2986_header,context2987_header,context2988_header,context2989_header,context2990_header,context2992_header,context2993_header,context2994_header,context2995_header,context2996_header,context2997_header,context2998_header,context2999_header,context3000_header,context3001_header,context3003_header,context3004_header,context3005_header,context3006_header,context3007_header,context3008_header,context3009_header,context3010_header,context3011_header,context3012_header,context2792_header,context2906_header,context2907_header,context2908_header,context2909_header,context2910_header,context2911_header,context2912_header,context2913_header,context2914_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 109).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2967,none),(2968,some (fanBlockRows 1100)),(2969,some (fanBlockRows 1111)),(2970,some (fanBlockRows 1122)),(2971,some (fanBlockRows 1130)),(2972,some (fanBlockRows 1141)),(2973,some (fanBlockRows 1152)),(2974,some (fanBlockRows 1163)),(2975,some (fanBlockRows 1174)),(2976,some (fanBlockRows 1185)),(2977,some (fanBlockRows 1090)),(2978,some (fanBlockRows 1091)),(2979,some (fanBlockRows 1092)),(2980,some (fanBlockRows 1093)),(2981,some (fanBlockRows 1094)),(2982,some (fanBlockRows 1095)),(2983,some (fanBlockRows 1096)),(2984,some (fanBlockRows 1097)),(2985,some (fanBlockRows 1098)),(2986,some (fanBlockRows 1099)),(2987,some (fanBlockRows 1101)),(2988,some (fanBlockRows 1102)),(2989,some (fanBlockRows 1103)),(2990,some (fanBlockRows 1104)),(2991,some (fanBlockRows 1105)),(2992,some (fanBlockRows 1106)),(2993,some (fanBlockRows 1107)),(2994,some (fanBlockRows 1108)),(2995,some (fanBlockRows 1109)),(2996,some (fanBlockRows 1110)),(2997,some (fanBlockRows 1112)),(2998,some (fanBlockRows 1113)),(2999,some (fanBlockRows 1114)),(3000,some (fanBlockRows 1115)),(3001,some (fanBlockRows 1116)),(3002,some (fanBlockRows 1117)),(3003,some (fanBlockRows 1118)),(3004,some (fanBlockRows 1119)),(3005,some (fanBlockRows 1120)),(3006,some (fanBlockRows 1121)),(3007,some (fanBlockRows 1123)),(3008,some (fanBlockRows 1124)),(3009,some (fanBlockRows 1125)),(3010,some (fanBlockRows 1126)),(3011,some (fanBlockRows 1127)),(3012,some (fanBlockRows 59)),(3013,some (fanBlockRows 59)),(3014,some (fanBlockRows 59)),(3015,some (fanBlockRows 1128)),(3016,some (fanBlockRows 1129)),(3017,some (fanBlockRows 1131)),(3018,some (fanBlockRows 1132)),(3019,some (fanBlockRows 1133)),(3020,some (fanBlockRows 1134)),(3021,some (fanBlockRows 1135)),(3022,some (fanBlockRows 1136)),(3023,some (fanBlockRows 1137)),(3024,some (fanBlockRows 1138)),(3025,some (fanBlockRows 1139)),(3026,some (fanBlockRows 1140)),(3027,some (fanBlockRows 1142)),(3028,some (fanBlockRows 1143)),(3029,some (fanBlockRows 1144)),(3030,some (fanBlockRows 1145)),(3031,some (fanBlockRows 1146)),(3032,some (fanBlockRows 1147)),(3033,some (fanBlockRows 1148)),(3034,some (fanBlockRows 1149)),(3035,some (fanBlockRows 1150)),(3036,some (fanBlockRows 1151)),(3037,some (fanBlockRows 1153)),(3038,some (fanBlockRows 1154)),(3039,some (fanBlockRows 1155)),(3040,some (fanBlockRows 1156)),(3041,some (fanBlockRows 1157)),(3042,some (fanBlockRows 1158)),(3043,some (fanBlockRows 1159)),(3044,some (fanBlockRows 1160)),(3045,some (fanBlockRows 1161)),(3046,some (fanBlockRows 1162)),(3047,some (fanBlockRows 1164)),(3048,some (fanBlockRows 1165)),(3049,some (fanBlockRows 1166)),(3050,some (fanBlockRows 1167)),(3051,some (fanBlockRows 1168)),(3052,some (fanBlockRows 1169)),(3053,some (fanBlockRows 1170)),(3054,some (fanBlockRows 1171)),(3055,some (fanBlockRows 1172)),(3056,some (fanBlockRows 1173)),(3057,some (fanBlockRows 1175)),(3058,some (fanBlockRows 1176)),(3059,some (fanBlockRows 1177)),(3060,some (fanBlockRows 1178)),(3061,some (fanBlockRows 1179)),(3062,some (fanBlockRows 1180)),(3063,some (fanBlockRows 1181)),(3064,some (fanBlockRows 1182)),(3065,some (fanBlockRows 1183)),(3066,some (fanBlockRows 1184)),(3067,some (fanBlockRows 1080)),(3068,some (fanBlockRows 1081)),(3069,some (fanBlockRows 1082)),(3070,some (fanBlockRows 1083)),(3071,some (fanBlockRows 1084)),(3072,some (fanBlockRows 1085)),(3073,some (fanBlockRows 1086)),(3074,some (fanBlockRows 1087)),(3075,some (fanBlockRows 1088)),(3076,some (fanBlockRows 1089)),(3077,none),(3078,none)]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step04.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 113).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step04.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step04.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step04

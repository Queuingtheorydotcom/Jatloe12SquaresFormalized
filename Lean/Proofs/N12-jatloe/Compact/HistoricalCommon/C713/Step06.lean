import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step06
import Compact.HistoricalCommon.C713.Step06Groups00
import Compact.HistoricalCommon.C713.Step06Groups01
import Compact.HistoricalCommon.C713.Step06Groups02
import Compact.HistoricalCommon.C713.Step06Groups03
import Compact.HistoricalCommon.C713.Step06Groups04
import Compact.HistoricalCommon.C713.Step06Groups05
import Compact.HistoricalCommon.C713.Step06Groups06
import Compact.HistoricalCommon.C713.Step06Groups07
import Compact.HistoricalCommon.C713.Step06Groups08
import Compact.HistoricalCommon.C713.Step06Groups09

namespace N12Compact.HistoricalCommon.C713.Step06
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 26 (.neighborCut 18 .leaf (.neighborCut 4 (.sourceCut 13 .leaf .leaf) (.neighborCut 5 (.sourceCut 13 (.neighborCut 2 .leaf .leaf) .leaf) (.neighborCut 10 (.sourceCut 13 .leaf (.neighborCut 5 (.sourceCut 6 .leaf .leaf) .leaf)) (.neighborCut 19 .leaf (.sourceCut 13 (.neighborCut 9 .leaf (.neighborCut 5 .leaf (.neighborCut 2 .leaf .leaf))) .leaf)))))) (.neighborCut 9 (.sourceCut 13 (.neighborCut 4 .leaf .leaf) (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf))) (.neighborCut 9 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 19 (.sourceCut 13 (.neighborCut 4 .leaf (.neighborCut 5 .leaf .leaf)) (.sourceCut 3 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 9 (.sourceCut 6 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 10 .leaf (.neighborCut 9 .leaf (.neighborCut 5 .leaf (.sourceCut 13 .leaf (.neighborCut 2 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,53,0,75⟩ scopes := by decide +kernel

theorem covered (i : Fin 53) (j : Fin 75) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 53) (j : Fin 75) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context3014_header,context3090_header,context3091_header,context3092_header,context3093_header,context3094_header,context3095_header,context3096_header,context3097_header,context3098_header,context3099_header,context3100_header,context3101_header,context3102_header,context3103_header,context3104_header,context3105_header,context3106_header,context3107_header,context3108_header,context3109_header,context3110_header,context3111_header,context3112_header,context3113_header,context3114_header,context3115_header,context3116_header,context3117_header,context3118_header,context3119_header,context3120_header,context3121_header,context3122_header,context3123_header,context3124_header,context3125_header,context3126_header,context3127_header,context3128_header,context3129_header,context3130_header,context3131_header,context3132_header,context3133_header,context3134_header,context3135_header,context3136_header,context3137_header,context3138_header,context3139_header,context3140_header,context3141_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 53).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3296,none),(3297,none),(3298,none),(3299,none),(3300,none),(3301,none),(3302,none),(3303,none),(3304,none),(3305,none),(3306,none),(3307,none),(3308,none),(3309,none),(3310,none),(3311,none),(3312,none),(3313,none),(3314,none),(3315,none),(3316,none),(3317,none),(3318,none),(3319,none),(3320,none),(3321,none),(3322,none),(3323,none),(3324,none),(3325,none),(3326,none),(3327,none),(3328,none),(3329,none),(3330,none),(3331,none),(3332,none),(3333,none),(3334,none),(3335,none),(3336,none),(3337,none),(3338,none),(3339,some (fanBlockRows 1186)),(3340,some (fanBlockRows 1187)),(3341,some (fanBlockRows 1188)),(3342,some (fanBlockRows 1189)),(3343,some (fanBlockRows 1190)),(3344,some (fanBlockRows 1191)),(3345,some (fanBlockRows 1192)),(3346,some (fanBlockRows 1193)),(3347,some (fanBlockRows 1194)),(3348,some (fanBlockRows 1195)),(3349,some (fanBlockRows 1196)),(3350,some (fanBlockRows 1197)),(3351,some (fanBlockRows 1198)),(3352,some (fanBlockRows 1199)),(3353,some (fanBlockRows 1200)),(3354,some (fanBlockRows 1201)),(3355,some (fanBlockRows 1202)),(3356,some (fanBlockRows 1203)),(3357,some (fanBlockRows 1204)),(3358,some (fanBlockRows 1205)),(3359,some (fanBlockRows 1206)),(3360,some (fanBlockRows 1207)),(3361,some (fanBlockRows 1208)),(3362,some (fanBlockRows 1209)),(3363,some (fanBlockRows 1210)),(3364,some (fanBlockRows 1211)),(3365,some (fanBlockRows 1212)),(3366,some (fanBlockRows 1213)),(3367,some (fanBlockRows 1214)),(3368,some (fanBlockRows 1215)),(3369,some (fanBlockRows 1216)),(3370,some (fanBlockRows 1217)),(3371,some (fanBlockRows 1218)),(3372,some (fanBlockRows 1219)),(3373,some (fanBlockRows 1220)),(3374,some (fanBlockRows 1221)),(3375,some (fanBlockRows 1222)),(3376,some (fanBlockRows 1223)),(3377,some (fanBlockRows 1224)),(3378,some (fanBlockRows 1225)),(3379,some (fanBlockRows 1226)),(3380,some (fanBlockRows 1227)),(3381,some (fanBlockRows 1228)),(3382,some (fanBlockRows 1229)),(3383,some (fanBlockRows 1230)),(3384,some (fanBlockRows 1231)),(3385,some (fanBlockRows 1232)),(3386,some (fanBlockRows 1233)),(3387,some (fanBlockRows 1234)),(3388,some (fanBlockRows 1235)),(3389,some (fanBlockRows 1236)),(3390,some (fanBlockRows 1237)),(3391,some (fanBlockRows 1238)),(3392,none),(3393,none),(3394,none),(3395,none),(3396,none),(3397,none)]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step06.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 75).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain1_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step06.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step06.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain1_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain1_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step06

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step07
import Compact.HistoricalCommon.C713.Step07Groups00
import Compact.HistoricalCommon.C713.Step07Groups01
import Compact.HistoricalCommon.C713.Step07Groups02
import Compact.HistoricalCommon.C713.Step07Groups03
import Compact.HistoricalCommon.C713.Step07Groups04

namespace N12Compact.HistoricalCommon.C713.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 3 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 27 .leaf (.sourceCut 51 .leaf (.sourceCut 25 (.neighborCut 27 .leaf (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.sourceCut 12 .leaf .leaf)))) (.sourceCut 13 (.neighborCut 27 .leaf (.sourceCut 6 .leaf .leaf)) (.neighborCut 27 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,102,0,109⟩ scopes := by decide +kernel

theorem covered (i : Fin 102) (j : Fin 109) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 102) (j : Fin 109) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context3142_header,context3264_header,context3275_header,context3286_header,context3297_header,context3308_header,context3319_header,context3330_header,context3341_header,context3352_header,context3254_header,context3255_header,context3256_header,context3257_header,context3258_header,context3259_header,context3260_header,context3261_header,context3262_header,context3263_header,context3265_header,context3266_header,context3267_header,context3268_header,context3269_header,context3270_header,context3271_header,context3272_header,context3273_header,context3274_header,context3276_header,context3277_header,context3278_header,context3279_header,context3280_header,context3281_header,context3282_header,context3283_header,context3284_header,context3285_header,context3287_header,context3288_header,context3289_header,context3290_header,context3291_header,context3292_header,context3293_header,context3294_header,context3295_header,context3296_header,context3298_header,context3299_header,context3300_header,context3301_header,context3302_header,context3303_header,context3304_header,context3305_header,context3306_header,context3307_header,context3309_header,context3310_header,context3311_header,context3312_header,context3313_header,context3314_header,context3315_header,context3316_header,context3317_header,context3318_header,context3320_header,context3321_header,context3322_header,context3323_header,context3324_header,context3325_header,context3326_header,context3327_header,context3328_header,context3329_header,context3331_header,context3332_header,context3333_header,context3334_header,context3335_header,context3336_header,context3337_header,context3338_header,context3339_header,context3340_header,context3342_header,context3343_header,context3344_header,context3345_header,context3346_header,context3347_header,context3348_header,context3349_header,context3350_header,context3351_header,context3252_header,context3253_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 102).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3398,some (fanBlockRows 59)),(3399,some (fanBlockRows 59)),(3400,some (fanBlockRows 59)),(3401,some (fanBlockRows 59)),(3402,some (fanBlockRows 59)),(3403,some (fanBlockRows 59)),(3404,some (fanBlockRows 59)),(3405,some (fanBlockRows 59)),(3406,some (fanBlockRows 59)),(3407,some (fanBlockRows 59)),(3408,some (fanBlockRows 59)),(3409,some (fanBlockRows 59)),(3410,some (fanBlockRows 59)),(3411,some (fanBlockRows 59)),(3412,some (fanBlockRows 59)),(3413,some (fanBlockRows 59)),(3414,some (fanBlockRows 59)),(3415,some (fanBlockRows 59)),(3416,some (fanBlockRows 59)),(3417,some (fanBlockRows 59)),(3418,some (fanBlockRows 59)),(3419,some (fanBlockRows 59)),(3420,some (fanBlockRows 59)),(3421,some (fanBlockRows 59)),(3422,some (fanBlockRows 59)),(3423,some (fanBlockRows 59)),(3424,some (fanBlockRows 59)),(3425,some (fanBlockRows 59)),(3426,some (fanBlockRows 59)),(3427,some (fanBlockRows 59)),(3428,some (fanBlockRows 59)),(3429,some (fanBlockRows 59)),(3430,some (fanBlockRows 59)),(3431,some (fanBlockRows 59)),(3432,some (fanBlockRows 59)),(3433,some (fanBlockRows 59)),(3434,some (fanBlockRows 1239)),(3435,some (fanBlockRows 1240)),(3436,some (fanBlockRows 59)),(3437,some (fanBlockRows 59)),(3438,some (fanBlockRows 59)),(3439,some (fanBlockRows 59)),(3440,some (fanBlockRows 59)),(3441,some (fanBlockRows 59)),(3442,some (fanBlockRows 59)),(3443,some (fanBlockRows 59)),(3444,some (fanBlockRows 59)),(3445,some (fanBlockRows 59)),(3446,some (fanBlockRows 59)),(3447,some (fanBlockRows 59)),(3448,some (fanBlockRows 59)),(3449,some (fanBlockRows 59)),(3450,some (fanBlockRows 59)),(3451,some (fanBlockRows 59)),(3452,some (fanBlockRows 59)),(3453,some (fanBlockRows 1241)),(3454,some (fanBlockRows 1242)),(3455,some (fanBlockRows 1243)),(3456,some (fanBlockRows 1244)),(3457,some (fanBlockRows 1245)),(3458,some (fanBlockRows 1246)),(3459,some (fanBlockRows 1247)),(3460,some (fanBlockRows 1248)),(3461,some (fanBlockRows 1249)),(3462,some (fanBlockRows 1250)),(3463,some (fanBlockRows 1251)),(3464,some (fanBlockRows 1252)),(3465,some (fanBlockRows 1253)),(3466,some (fanBlockRows 1254)),(3467,some (fanBlockRows 1255)),(3468,some (fanBlockRows 1256)),(3469,some (fanBlockRows 1257)),(3470,some (fanBlockRows 1258)),(3471,some (fanBlockRows 1259)),(3472,some (fanBlockRows 1260)),(3473,some (fanBlockRows 1261)),(3474,some (fanBlockRows 1262)),(3475,some (fanBlockRows 1263)),(3476,some (fanBlockRows 1264)),(3477,some (fanBlockRows 1265)),(3478,some (fanBlockRows 1266)),(3479,some (fanBlockRows 1267)),(3480,some (fanBlockRows 59)),(3481,some (fanBlockRows 59)),(3482,some (fanBlockRows 59)),(3483,some (fanBlockRows 59)),(3484,some (fanBlockRows 59)),(3485,some (fanBlockRows 59)),(3486,some (fanBlockRows 59)),(3487,some (fanBlockRows 59)),(3488,some (fanBlockRows 59)),(3489,some (fanBlockRows 59)),(3490,some (fanBlockRows 59)),(3491,some (fanBlockRows 59)),(3492,some (fanBlockRows 59)),(3493,some (fanBlockRows 59)),(3494,some (fanBlockRows 59)),(3495,some (fanBlockRows 59)),(3496,some (fanBlockRows 59)),(3497,some (fanBlockRows 59)),(3498,some (fanBlockRows 59)),(3499,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step07.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 109).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain6_5Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step07.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step07.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain6_5Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain6_5Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step07

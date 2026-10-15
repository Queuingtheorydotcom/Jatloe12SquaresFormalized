import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step03
import Compact.HistoricalCommon.C973.Step03Groups00
import Compact.HistoricalCommon.C973.Step03Groups01
import Compact.HistoricalCommon.C973.Step03Groups02
import Compact.HistoricalCommon.C973.Step03Groups03
import Compact.HistoricalCommon.C973.Step03Groups04
import Compact.HistoricalCommon.C973.Step03Groups05
import Compact.HistoricalCommon.C973.Step03Groups06
import Compact.HistoricalCommon.C973.Step03Groups07
import Compact.HistoricalCommon.C973.Step03Groups08

namespace N12Compact.HistoricalCommon.C973.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf))))) (.sourceCut 8 (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.sourceCut 4 (.neighborCut 8 .leaf (.sourceCut 2 .leaf .leaf)) (.neighborCut 8 .leaf .leaf)))) (.sourceCut 8 (.neighborCut 16 .leaf (.neighborCut 16 .leaf .leaf)) (.neighborCut 32 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)) (.sourceCut 8 (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 16 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8071_header,context8146_header,context8157_header,context8168_header,context8179_header,context8190_header,context8195_header,context8196_header,context8197_header,context8198_header,context8136_header,context8137_header,context8138_header,context8139_header,context8140_header,context8141_header,context8142_header,context8143_header,context8144_header,context8145_header,context8147_header,context8148_header,context8149_header,context8150_header,context8151_header,context8152_header,context8153_header,context8154_header,context8155_header,context8156_header,context8158_header,context8159_header,context8160_header,context8161_header,context8162_header,context8163_header,context8164_header,context8165_header,context8166_header,context8167_header,context8169_header,context8170_header,context8171_header,context8172_header,context8173_header,context8174_header,context8175_header,context8176_header,context8177_header,context8178_header,context8180_header,context8181_header,context8182_header,context8183_header,context8184_header,context8185_header,context8186_header,context8187_header,context8188_header,context8189_header,context8191_header,context8192_header,context8193_header,context8194_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5966,some (fanBlockRows 3247)),(5967,some (fanBlockRows 3258)),(5968,some (fanBlockRows 3269)),(5969,some (fanBlockRows 3280)),(5970,some (fanBlockRows 3291)),(5971,some (fanBlockRows 3302)),(5972,some (fanBlockRows 3307)),(5973,some (fanBlockRows 3308)),(5974,some (fanBlockRows 3309)),(5975,some (fanBlockRows 3310)),(5976,some (fanBlockRows 3248)),(5977,some (fanBlockRows 3249)),(5978,some (fanBlockRows 3250)),(5979,some (fanBlockRows 3251)),(5980,some (fanBlockRows 3252)),(5981,some (fanBlockRows 3253)),(5982,some (fanBlockRows 3254)),(5983,some (fanBlockRows 3255)),(5984,some (fanBlockRows 3256)),(5985,some (fanBlockRows 3257)),(5986,some (fanBlockRows 3259)),(5987,some (fanBlockRows 3260)),(5988,some (fanBlockRows 3261)),(5989,some (fanBlockRows 3262)),(5990,some (fanBlockRows 3263)),(5991,some (fanBlockRows 3264)),(5992,some (fanBlockRows 3265)),(5993,some (fanBlockRows 3266)),(5994,some (fanBlockRows 3267)),(5995,some (fanBlockRows 3268)),(5996,some (fanBlockRows 3270)),(5997,some (fanBlockRows 3271)),(5998,some (fanBlockRows 3272)),(5999,some (fanBlockRows 3273)),(6000,some (fanBlockRows 3274)),(6001,some (fanBlockRows 3275)),(6002,some (fanBlockRows 3276)),(6003,some (fanBlockRows 3277)),(6004,some (fanBlockRows 3278)),(6005,some (fanBlockRows 3279)),(6006,some (fanBlockRows 3281)),(6007,some (fanBlockRows 3282)),(6008,some (fanBlockRows 3283)),(6009,some (fanBlockRows 3284)),(6010,some (fanBlockRows 3285)),(6011,some (fanBlockRows 3286)),(6012,some (fanBlockRows 3287)),(6013,some (fanBlockRows 3288)),(6014,some (fanBlockRows 3289)),(6015,some (fanBlockRows 3290)),(6016,some (fanBlockRows 3292)),(6017,some (fanBlockRows 3293)),(6018,some (fanBlockRows 3294)),(6019,some (fanBlockRows 3295)),(6020,some (fanBlockRows 3296)),(6021,some (fanBlockRows 3297)),(6022,some (fanBlockRows 3298)),(6023,some (fanBlockRows 3299)),(6024,some (fanBlockRows 3300)),(6025,some (fanBlockRows 3301)),(6026,some (fanBlockRows 3303)),(6027,some (fanBlockRows 3304)),(6028,some (fanBlockRows 3305)),(6029,some (fanBlockRows 3306))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step03.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain6_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step03.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step03.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain6_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain6_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step03

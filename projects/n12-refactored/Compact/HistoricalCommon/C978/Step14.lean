import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step14
import Compact.HistoricalCommon.C978.Step14Groups00
import Compact.HistoricalCommon.C978.Step14Groups01
import Compact.HistoricalCommon.C978.Step14Groups02

namespace N12Compact.HistoricalCommon.C978.Step14
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 5 (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 3 .leaf .leaf))))))) (.sourceCut 5 .leaf (.sourceCut 11 .leaf .leaf)))

theorem partition_checked : partition.Check ⟨0,42,0,12⟩ scopes := by decide +kernel

theorem covered (i : Fin 42) (j : Fin 12) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 42) (j : Fin 12) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9165_header,context9176_header,context9187_header,context9191_header,context9192_header,context9193_header,context9194_header,context9195_header,context9196_header,context9143_header,context9156_header,context9157_header,context9158_header,context9159_header,context9160_header,context9161_header,context9162_header,context9163_header,context9164_header,context9166_header,context9167_header,context9168_header,context9169_header,context9170_header,context9171_header,context9172_header,context9173_header,context9174_header,context9175_header,context9177_header,context9178_header,context9179_header,context9180_header,context9181_header,context9182_header,context9183_header,context9184_header,context9185_header,context9186_header,context9188_header,context9189_header,context9190_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 42).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8053,none),(8054,some (fanBlockRows 3876)),(8055,some (fanBlockRows 3877)),(8056,some (fanBlockRows 59)),(8057,some (fanBlockRows 59)),(8058,some (fanBlockRows 59)),(8059,some (fanBlockRows 59)),(8060,some (fanBlockRows 59)),(8061,some (fanBlockRows 59)),(8062,some (fanBlockRows 59)),(8063,some (fanBlockRows 59)),(8064,some (fanBlockRows 59)),(8065,some (fanBlockRows 59)),(8066,some (fanBlockRows 59)),(8067,some (fanBlockRows 59)),(8068,some (fanBlockRows 59)),(8069,some (fanBlockRows 59)),(8070,some (fanBlockRows 59)),(8071,some (fanBlockRows 59)),(8072,some (fanBlockRows 59)),(8073,some (fanBlockRows 59)),(8074,some (fanBlockRows 59)),(8075,some (fanBlockRows 59)),(8076,some (fanBlockRows 59)),(8077,some (fanBlockRows 59)),(8078,some (fanBlockRows 59)),(8079,some (fanBlockRows 59)),(8080,some (fanBlockRows 59)),(8081,some (fanBlockRows 59)),(8082,some (fanBlockRows 59)),(8083,some (fanBlockRows 59)),(8084,some (fanBlockRows 59)),(8085,some (fanBlockRows 59)),(8086,some (fanBlockRows 59)),(8087,some (fanBlockRows 59)),(8088,some (fanBlockRows 59)),(8089,some (fanBlockRows 59)),(8090,some (fanBlockRows 59)),(8091,some (fanBlockRows 59)),(8092,some (fanBlockRows 59)),(8093,some (fanBlockRows 59)),(8094,some (fanBlockRows 59)),(8095,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step14.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 12).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain7_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step14.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step14.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain7_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain7_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step14

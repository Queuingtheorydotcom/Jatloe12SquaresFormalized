import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step15
import Compact.HistoricalCommon.C978.Step15Groups00
import Compact.HistoricalCommon.C978.Step15Groups01

namespace N12Compact.HistoricalCommon.C978.Step15
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 7 (.sourceCut 1 .leaf (.sourceCut 1 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf)))) (.neighborCut 8 .leaf (.neighborCut 15 .leaf .leaf)))

theorem partition_checked : partition.Check ⟨0,3,0,60⟩ scopes := by decide +kernel

theorem covered (i : Fin 3) (j : Fin 60) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 3) (j : Fin 60) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9197_header,context9258_header,context9259_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 3).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8096,some (fanBlockRows 59)),(8097,some (fanBlockRows 59)),(8098,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step15.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 60).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain10_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step15.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step15.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain10_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain10_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step15

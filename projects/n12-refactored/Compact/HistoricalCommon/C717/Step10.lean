import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step10
import Compact.HistoricalCommon.C717.Step10Groups00
import Compact.HistoricalCommon.C717.Step10Groups01
import Compact.HistoricalCommon.C717.Step10Groups02

namespace N12Compact.HistoricalCommon.C717.Step10
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 14 (.sourceCut 6 (.neighborCut 7 .leaf (.sourceCut 3 .leaf .leaf)) .leaf) (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 4 .leaf (.neighborCut 7 .leaf (.neighborCut 29 .leaf .leaf))))))

theorem partition_checked : partition.Check ⟨0,13,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 13) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 13) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context3908_header,context3909_header,context3910_header,context3911_header,context3912_header,context3913_header,context3914_header,context3900_header,context3903_header,context3904_header,context3905_header,context3906_header,context3907_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 13).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5625,none),(5626,none),(5627,none),(5628,some (fanBlockRows 1468)),(5629,some (fanBlockRows 1469)),(5630,some (fanBlockRows 1470)),(5631,some (fanBlockRows 1471)),(5632,some (fanBlockRows 1472)),(5633,some (fanBlockRows 1473)),(5634,some (fanBlockRows 59)),(5635,some (fanBlockRows 59)),(5636,some (fanBlockRows 59)),(5637,some (fanBlockRows 59)),(5638,some (fanBlockRows 59)),(5639,some (fanBlockRows 59)),(5640,some (fanBlockRows 59)),(5641,none),(5642,none)]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step10.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain11_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step10.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step10.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain11_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain11_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step10

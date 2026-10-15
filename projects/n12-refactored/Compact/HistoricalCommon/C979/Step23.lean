import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step23
import Compact.HistoricalCommon.C979.Step23Groups00

namespace N12Compact.HistoricalCommon.C979.Step23
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0]

def scopes : List Scope :=
  [group0_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  .leaf

theorem partition_checked : partition.Check ⟨0,25,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 25) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 25) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11487_header,context11626_header,context11632_header,context11633_header,context11634_header,context11635_header,context11636_header,context11637_header,context11638_header,context11639_header,context11616_header,context11617_header,context11618_header,context11619_header,context11620_header,context11621_header,context11622_header,context11623_header,context11624_header,context11625_header,context11627_header,context11628_header,context11629_header,context11630_header,context11631_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 25).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11459,some (fanBlockRows 59)),(11460,some (fanBlockRows 59)),(11461,some (fanBlockRows 59)),(11462,some (fanBlockRows 59)),(11463,some (fanBlockRows 59)),(11464,some (fanBlockRows 59)),(11465,some (fanBlockRows 59)),(11466,some (fanBlockRows 59)),(11467,some (fanBlockRows 59)),(11468,some (fanBlockRows 59)),(11469,some (fanBlockRows 59)),(11470,some (fanBlockRows 59)),(11471,some (fanBlockRows 59)),(11472,some (fanBlockRows 59)),(11473,some (fanBlockRows 59)),(11474,some (fanBlockRows 4900)),(11475,some (fanBlockRows 4901)),(11476,some (fanBlockRows 4902)),(11477,some (fanBlockRows 4903)),(11478,some (fanBlockRows 4904)),(11479,some (fanBlockRows 4905)),(11480,some (fanBlockRows 4906)),(11481,some (fanBlockRows 4907)),(11482,some (fanBlockRows 4908)),(11483,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step23.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step23.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step23.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step23

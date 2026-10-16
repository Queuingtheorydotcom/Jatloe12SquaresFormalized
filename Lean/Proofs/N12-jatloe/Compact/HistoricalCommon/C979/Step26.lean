import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step26
import Compact.HistoricalCommon.C979.Step26Groups00

namespace N12Compact.HistoricalCommon.C979.Step26
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

theorem partition_checked : partition.Check ⟨0,67,0,42⟩ scopes := by decide +kernel

theorem covered (i : Fin 67) (j : Fin 42) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 67) (j : Fin 42) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11715_header,context11778_header,context11799_header,context11821_header,context11843_header,context11865_header,context11880_header,context11882_header,context11884_header,context11886_header,context11759_header,context11761_header,context11763_header,context11765_header,context11767_header,context11769_header,context11771_header,context11773_header,context11775_header,context11777_header,context11780_header,context11782_header,context11784_header,context11786_header,context11788_header,context11790_header,context11792_header,context11794_header,context11796_header,context11798_header,context11801_header,context11803_header,context11805_header,context11807_header,context11809_header,context11811_header,context11813_header,context11815_header,context11817_header,context11819_header,context11823_header,context11825_header,context11827_header,context11829_header,context11831_header,context11833_header,context11835_header,context11837_header,context11839_header,context11841_header,context11845_header,context11847_header,context11849_header,context11851_header,context11853_header,context11855_header,context11857_header,context11859_header,context11861_header,context11863_header,context11867_header,context11869_header,context11871_header,context11873_header,context11875_header,context11877_header,context11878_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 67).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3986,some (fanBlockRows 4951)),(8736,some (fanBlockRows 4952)),(8737,some (fanBlockRows 4953)),(8738,some (fanBlockRows 59)),(8739,some (fanBlockRows 59)),(8740,some (fanBlockRows 59)),(8741,some (fanBlockRows 59)),(8742,some (fanBlockRows 59)),(8743,some (fanBlockRows 59)),(8744,some (fanBlockRows 59)),(8745,some (fanBlockRows 59)),(8746,some (fanBlockRows 59)),(8747,some (fanBlockRows 59)),(8748,some (fanBlockRows 59)),(8749,some (fanBlockRows 59)),(8750,some (fanBlockRows 59)),(8751,some (fanBlockRows 59)),(8752,some (fanBlockRows 59)),(8753,some (fanBlockRows 59)),(8754,some (fanBlockRows 59)),(8755,some (fanBlockRows 59)),(8756,some (fanBlockRows 59)),(8757,some (fanBlockRows 59)),(8758,some (fanBlockRows 59)),(8759,some (fanBlockRows 59)),(8760,some (fanBlockRows 59)),(8761,some (fanBlockRows 59)),(8762,some (fanBlockRows 59)),(8763,some (fanBlockRows 59)),(8764,some (fanBlockRows 59)),(8765,some (fanBlockRows 59)),(8766,some (fanBlockRows 59)),(8767,some (fanBlockRows 59)),(8768,some (fanBlockRows 59)),(8769,some (fanBlockRows 59)),(8770,some (fanBlockRows 59)),(8771,some (fanBlockRows 59)),(8772,some (fanBlockRows 59)),(8773,some (fanBlockRows 59)),(8774,some (fanBlockRows 59)),(8775,some (fanBlockRows 59)),(8776,some (fanBlockRows 59)),(8777,some (fanBlockRows 59)),(8778,some (fanBlockRows 59)),(8779,some (fanBlockRows 59)),(8780,some (fanBlockRows 59)),(8781,some (fanBlockRows 59)),(8782,some (fanBlockRows 59)),(8783,some (fanBlockRows 59)),(8784,some (fanBlockRows 59)),(8785,some (fanBlockRows 59)),(8786,some (fanBlockRows 59)),(8787,some (fanBlockRows 59)),(8788,some (fanBlockRows 59)),(8789,some (fanBlockRows 59)),(8790,some (fanBlockRows 59)),(8791,some (fanBlockRows 59)),(8792,some (fanBlockRows 59)),(8793,some (fanBlockRows 59)),(8794,some (fanBlockRows 59)),(8795,some (fanBlockRows 59)),(8796,some (fanBlockRows 59)),(8797,some (fanBlockRows 59)),(8798,some (fanBlockRows 59)),(8799,some (fanBlockRows 59)),(8800,some (fanBlockRows 59)),(4098,some (fanBlockRows 4954))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step26.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 42).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain9_26Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step26.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step26.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain9_26Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain9_26Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step26

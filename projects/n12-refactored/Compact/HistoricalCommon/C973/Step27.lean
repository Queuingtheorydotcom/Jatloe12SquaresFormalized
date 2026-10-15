import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step27
import Compact.HistoricalCommon.C973.Step27Groups00

namespace N12Compact.HistoricalCommon.C973.Step27
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

theorem partition_checked : partition.Check ⟨0,22,0,9⟩ scopes := by decide +kernel

theorem covered (i : Fin 22) (j : Fin 9) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 22) (j : Fin 9) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8040_header,context8060_header,context8063_header,context8064_header,context8065_header,context8066_header,context8067_header,context8068_header,context8069_header,context8070_header,context8050_header,context8051_header,context8052_header,context8053_header,context8054_header,context8055_header,context8056_header,context8057_header,context8058_header,context8059_header,context8061_header,context8062_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 22).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6164,some (fanBlockRows 59)),(6165,some (fanBlockRows 59)),(6166,some (fanBlockRows 59)),(6167,some (fanBlockRows 59)),(6168,some (fanBlockRows 59)),(6169,some (fanBlockRows 59)),(6170,some (fanBlockRows 59)),(6171,some (fanBlockRows 59)),(6172,some (fanBlockRows 59)),(6173,some (fanBlockRows 59)),(6174,some (fanBlockRows 59)),(6175,some (fanBlockRows 59)),(6176,some (fanBlockRows 59)),(6177,some (fanBlockRows 59)),(6178,some (fanBlockRows 59)),(6179,some (fanBlockRows 59)),(6180,some (fanBlockRows 59)),(6181,some (fanBlockRows 59)),(6182,some (fanBlockRows 59)),(6183,some (fanBlockRows 59)),(6184,some (fanBlockRows 59)),(6185,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step27.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 9).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain6_24Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step27.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step27.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain6_24Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain6_24Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step27

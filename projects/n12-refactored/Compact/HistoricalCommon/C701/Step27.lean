import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step27
import Compact.HistoricalCommon.C701.Step27Groups00
import Compact.HistoricalCommon.C701.Step27Groups01
import Compact.HistoricalCommon.C701.Step27Groups02
import Compact.HistoricalCommon.C701.Step27Groups03

namespace N12Compact.HistoricalCommon.C701.Step27
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 8 (.neighborCut 2 (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)) (.neighborCut 2 .leaf (.neighborCut 4 .leaf (.neighborCut 9 .leaf (.neighborCut 9 .leaf (.neighborCut 4 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))))))))) .leaf)

theorem partition_checked : partition.Check ⟨0,17,0,35⟩ scopes := by decide +kernel

theorem covered (i : Fin 17) (j : Fin 35) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 17) (j : Fin 35) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1252_header,context1253_header,context1254_header,context1255_header,context1256_header,context1257_header,context1206_header,context1242_header,context1243_header,context1244_header,context1245_header,context1246_header,context1247_header,context1248_header,context1249_header,context1250_header,context1251_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 17).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(482,none),(483,none),(484,none),(485,none),(486,some (fanBlockRows 477)),(487,some (fanBlockRows 478)),(488,some (fanBlockRows 479)),(489,some (fanBlockRows 480)),(490,some (fanBlockRows 481)),(491,some (fanBlockRows 482)),(492,some (fanBlockRows 59)),(493,some (fanBlockRows 59)),(494,some (fanBlockRows 59)),(495,some (fanBlockRows 59)),(496,some (fanBlockRows 59)),(497,some (fanBlockRows 59)),(498,some (fanBlockRows 59)),(499,some (fanBlockRows 59)),(500,some (fanBlockRows 59)),(501,some (fanBlockRows 59)),(502,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step27.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 35).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain8_25Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step27.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step27.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain8_25Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain8_25Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step27

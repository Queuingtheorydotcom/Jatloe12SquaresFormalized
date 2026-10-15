import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step30
import Compact.HistoricalCommon.C701.Step30Groups00
import Compact.HistoricalCommon.C701.Step30Groups01
import Compact.HistoricalCommon.C701.Step30Groups02
import Compact.HistoricalCommon.C701.Step30Groups03
import Compact.HistoricalCommon.C701.Step30Groups04
import Compact.HistoricalCommon.C701.Step30Groups05

namespace N12Compact.HistoricalCommon.C701.Step30
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 3 (.neighborCut 5 (.sourceCut 1 .leaf (.sourceCut 1 .leaf (.neighborCut 2 .leaf .leaf))) (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))) (.sourceCut 4 (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.sourceCut 2 .leaf .leaf)))))) (.sourceCut 8 (.neighborCut 5 (.sourceCut 2 (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf)) (.sourceCut 2 .leaf .leaf)) .leaf) .leaf)))

theorem partition_checked : partition.Check ⟨0,31,0,10⟩ scopes := by decide +kernel

theorem covered (i : Fin 31) (j : Fin 10) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 31) (j : Fin 10) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1322_header,context1343_header,context1354_header,context1356_header,context1357_header,context1358_header,context1359_header,context1360_header,context1361_header,context1362_header,context1333_header,context1334_header,context1335_header,context1336_header,context1337_header,context1338_header,context1339_header,context1340_header,context1341_header,context1342_header,context1344_header,context1345_header,context1346_header,context1347_header,context1348_header,context1349_header,context1350_header,context1351_header,context1352_header,context1353_header,context1355_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 31).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1007,some (fanBlockRows 59)),(1008,some (fanBlockRows 59)),(1009,some (fanBlockRows 59)),(1010,some (fanBlockRows 59)),(1011,some (fanBlockRows 59)),(1012,some (fanBlockRows 59)),(1013,some (fanBlockRows 59)),(1014,some (fanBlockRows 59)),(1015,some (fanBlockRows 59)),(1016,some (fanBlockRows 59)),(1017,some (fanBlockRows 59)),(1018,some (fanBlockRows 59)),(1019,some (fanBlockRows 59)),(1020,some (fanBlockRows 59)),(1021,some (fanBlockRows 59)),(1022,some (fanBlockRows 59)),(1023,some (fanBlockRows 59)),(1024,some (fanBlockRows 59)),(1025,some (fanBlockRows 59)),(1026,some (fanBlockRows 59)),(1027,some (fanBlockRows 59)),(1028,some (fanBlockRows 59)),(1029,some (fanBlockRows 59)),(1030,some (fanBlockRows 59)),(1031,some (fanBlockRows 59)),(1032,some (fanBlockRows 59)),(1033,some (fanBlockRows 59)),(1034,some (fanBlockRows 59)),(1035,some (fanBlockRows 59)),(1036,some (fanBlockRows 59)),(1037,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step30.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 10).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain11_28Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step30.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step30.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain11_28Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain11_28Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step30

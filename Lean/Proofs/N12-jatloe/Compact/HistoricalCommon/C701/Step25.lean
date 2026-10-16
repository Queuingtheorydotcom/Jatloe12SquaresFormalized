import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step25
import Compact.HistoricalCommon.C701.Step25Groups00
import Compact.HistoricalCommon.C701.Step25Groups01
import Compact.HistoricalCommon.C701.Step25Groups02
import Compact.HistoricalCommon.C701.Step25Groups03
import Compact.HistoricalCommon.C701.Step25Groups04
import Compact.HistoricalCommon.C701.Step25Groups05

namespace N12Compact.HistoricalCommon.C701.Step25
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 2 (.sourceCut 3 .leaf .leaf) (.neighborCut 2 (.sourceCut 3 .leaf (.neighborCut 1 .leaf .leaf)) (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 3 (.neighborCut 8 .leaf (.neighborCut 2 .leaf (.sourceCut 1 (.neighborCut 2 .leaf .leaf) (.neighborCut 2 .leaf (.sourceCut 1 .leaf .leaf))))) (.neighborCut 2 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf))))))))))))

theorem partition_checked : partition.Check ⟨0,6,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 6) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 6) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1074_header,context1142_header,context1143_header,context1144_header,context1145_header,context1146_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 6).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(378,none),(379,none),(380,none),(381,none),(382,some (fanBlockRows 450)),(383,some (fanBlockRows 451)),(384,some (fanBlockRows 452)),(385,some (fanBlockRows 453)),(386,some (fanBlockRows 454)),(387,some (fanBlockRows 455)),(388,none),(389,none),(390,none),(391,none),(392,none),(393,none),(394,none),(395,none),(396,none),(397,none),(398,none),(399,none),(400,none),(401,none),(402,none),(403,none),(404,none),(405,none),(406,none),(407,none),(408,none),(409,none),(410,none),(411,none),(412,none),(413,none),(414,none),(415,none),(416,none),(417,none),(418,none),(419,none),(420,none),(421,none),(422,none),(423,none),(424,none),(425,none),(426,none),(427,none),(428,none),(429,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step25.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain5_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step25.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step25.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain5_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain5_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step25

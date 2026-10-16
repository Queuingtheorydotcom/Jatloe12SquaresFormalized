import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step12
import Compact.HistoricalCommon.C701.Step12Groups00
import Compact.HistoricalCommon.C701.Step12Groups01
import Compact.HistoricalCommon.C701.Step12Groups02
import Compact.HistoricalCommon.C701.Step12Groups03
import Compact.HistoricalCommon.C701.Step12Groups04
import Compact.HistoricalCommon.C701.Step12Groups05
import Compact.HistoricalCommon.C701.Step12Groups06
import Compact.HistoricalCommon.C701.Step12Groups07
import Compact.HistoricalCommon.C701.Step12Groups08

namespace N12Compact.HistoricalCommon.C701.Step12
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 1 (.sourceCut 3 .leaf .leaf) (.neighborCut 2 .leaf (.neighborCut 4 .leaf (.neighborCut 7 .leaf (.sourceCut 3 (.neighborCut 7 .leaf (.neighborCut 2 .leaf (.neighborCut 2 (.sourceCut 1 .leaf .leaf) (.neighborCut 4 (.sourceCut 1 .leaf .leaf) (.neighborCut 3 (.sourceCut 1 .leaf .leaf) (.neighborCut 4 (.sourceCut 1 .leaf .leaf) (.neighborCut 4 (.sourceCut 1 .leaf .leaf) (.neighborCut 4 (.sourceCut 1 .leaf .leaf) (.neighborCut 7 (.sourceCut 1 .leaf .leaf) (.neighborCut 4 (.sourceCut 1 .leaf .leaf) .leaf)))))))))) (.neighborCut 7 .leaf (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 2 .leaf (.neighborCut 2 (.sourceCut 1 .leaf .leaf) (.neighborCut 4 (.sourceCut 1 (.neighborCut 2 .leaf .leaf) .leaf) .leaf)))))))))))))

theorem partition_checked : partition.Check ⟨0,6,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 6) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 6) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context414_header,context521_header,context522_header,context523_header,context524_header,context525_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 6).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1380,some (fanBlockRows 166)),(1381,some (fanBlockRows 167)),(1382,some (fanBlockRows 168)),(1383,some (fanBlockRows 169)),(1384,some (fanBlockRows 170)),(1385,some (fanBlockRows 171)),(1386,none),(1387,none),(1388,none),(1389,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step12.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain8_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step12.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step12.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain8_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain8_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step12

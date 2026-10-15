import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step13
import Compact.HistoricalCommon.C701.Step13Groups00
import Compact.HistoricalCommon.C701.Step13Groups01
import Compact.HistoricalCommon.C701.Step13Groups02
import Compact.HistoricalCommon.C701.Step13Groups03
import Compact.HistoricalCommon.C701.Step13Groups04
import Compact.HistoricalCommon.C701.Step13Groups05
import Compact.HistoricalCommon.C701.Step13Groups06

namespace N12Compact.HistoricalCommon.C701.Step13
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 9 (.neighborCut 2 (.sourceCut 2 .leaf (.sourceCut 1 .leaf (.sourceCut 1 .leaf (.sourceCut 2 .leaf .leaf)))) (.neighborCut 1 (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)) (.neighborCut 2 (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)) (.neighborCut 2 (.sourceCut 2 .leaf (.sourceCut 2 .leaf .leaf)) .leaf)))) (.sourceCut 5 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf))) (.sourceCut 5 (.neighborCut 2 (.sourceCut 2 .leaf .leaf) (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf)))) .leaf)))

theorem partition_checked : partition.Check ⟨0,39,0,10⟩ scopes := by decide +kernel

theorem covered (i : Fin 39) (j : Fin 10) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 39) (j : Fin 10) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context281_header,context283_header,context285_header,context541_header,context542_header,context526_header,context537_header,context538_header,context292_header,context294_header,context296_header,context298_header,context300_header,context302_header,context539_header,context540_header,context306_header,context308_header,context310_header,context312_header,context314_header,context316_header,context318_header,context320_header,context322_header,context324_header,context326_header,context328_header,context330_header,context332_header,context334_header,context336_header,context338_header,context340_header,context342_header,context344_header,context346_header,context348_header,context350_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 39).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1577,none),(1578,none),(1579,none),(1580,none),(1581,none),(1582,some (fanBlockRows 59)),(1583,some (fanBlockRows 59)),(1584,some (fanBlockRows 59)),(1585,some (fanBlockRows 177)),(1586,some (fanBlockRows 178)),(1587,some (fanBlockRows 172)),(1588,some (fanBlockRows 173)),(1589,some (fanBlockRows 174)),(1590,some (fanBlockRows 59)),(1591,some (fanBlockRows 59)),(1592,some (fanBlockRows 59)),(1593,some (fanBlockRows 59)),(1594,some (fanBlockRows 59)),(1595,some (fanBlockRows 59)),(1596,some (fanBlockRows 175)),(1597,some (fanBlockRows 176)),(1598,some (fanBlockRows 59)),(1599,some (fanBlockRows 59)),(1600,some (fanBlockRows 59)),(1601,some (fanBlockRows 59)),(1602,some (fanBlockRows 59)),(1603,some (fanBlockRows 59)),(1604,some (fanBlockRows 59)),(1605,some (fanBlockRows 59)),(1606,some (fanBlockRows 59)),(1607,some (fanBlockRows 59)),(1608,some (fanBlockRows 59)),(1609,some (fanBlockRows 59)),(1610,some (fanBlockRows 59)),(1611,some (fanBlockRows 59)),(1612,some (fanBlockRows 59)),(1613,some (fanBlockRows 59)),(1614,some (fanBlockRows 59)),(1615,some (fanBlockRows 59)),(1616,some (fanBlockRows 59)),(1617,some (fanBlockRows 59)),(1618,some (fanBlockRows 59)),(1619,some (fanBlockRows 59)),(1620,some (fanBlockRows 59)),(1621,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step13.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 10).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain6_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step13.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step13.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain6_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain6_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step13

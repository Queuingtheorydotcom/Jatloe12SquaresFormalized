import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step02
import Compact.HistoricalCommon.C973.Step02Groups00
import Compact.HistoricalCommon.C973.Step02Groups01
import Compact.HistoricalCommon.C973.Step02Groups02
import Compact.HistoricalCommon.C973.Step02Groups03
import Compact.HistoricalCommon.C973.Step02Groups04
import Compact.HistoricalCommon.C973.Step02Groups05
import Compact.HistoricalCommon.C973.Step02Groups06
import Compact.HistoricalCommon.C973.Step02Groups07
import Compact.HistoricalCommon.C973.Step02Groups08

namespace N12Compact.HistoricalCommon.C973.Step02
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
  (.sourceCut 16 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 16 (.sourceCut 4 .leaf .leaf) (.neighborCut 8 (.sourceCut 4 .leaf .leaf) .leaf))) (.neighborCut 8 (.sourceCut 4 (.neighborCut 4 .leaf .leaf) .leaf) (.neighborCut 16 .leaf .leaf)))))) (.neighborCut 8 (.sourceCut 4 .leaf (.sourceCut 2 .leaf (.sourceCut 2 .leaf (.sourceCut 4 .leaf .leaf)))) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.sourceCut 4 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))) (.sourceCut 2 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))) (.sourceCut 2 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 16 .leaf (.sourceCut 4 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,32,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 32) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 32) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6538_header,context6543_header,context6547_header,context6548_header,context6549_header,context6550_header,context6551_header,context6552_header,context6553_header,context6471_header,context6536_header,context6537_header,context433_header,context435_header,context437_header,context439_header,context441_header,context443_header,context445_header,context447_header,context449_header,context451_header,context453_header,context455_header,context457_header,context6539_header,context6540_header,context6541_header,context6542_header,context6544_header,context6545_header,context6546_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 32).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1622,none),(1623,some (fanBlockRows 2531)),(1624,some (fanBlockRows 2536)),(1625,some (fanBlockRows 2540)),(1626,some (fanBlockRows 2541)),(1627,some (fanBlockRows 2542)),(1628,some (fanBlockRows 2543)),(1629,some (fanBlockRows 2544)),(1630,some (fanBlockRows 2545)),(1631,some (fanBlockRows 2546)),(1632,some (fanBlockRows 2528)),(1633,some (fanBlockRows 2529)),(1634,some (fanBlockRows 2530)),(1635,some (fanBlockRows 59)),(1636,some (fanBlockRows 59)),(1637,some (fanBlockRows 59)),(1638,some (fanBlockRows 59)),(1639,some (fanBlockRows 59)),(1640,some (fanBlockRows 59)),(1641,some (fanBlockRows 59)),(1642,some (fanBlockRows 59)),(1643,some (fanBlockRows 59)),(1644,some (fanBlockRows 59)),(1645,some (fanBlockRows 59)),(1646,some (fanBlockRows 59)),(1647,some (fanBlockRows 59)),(1648,some (fanBlockRows 2532)),(1649,some (fanBlockRows 2533)),(1650,some (fanBlockRows 2534)),(1651,some (fanBlockRows 2535)),(1652,some (fanBlockRows 2537)),(1653,some (fanBlockRows 2538)),(1654,some (fanBlockRows 2539)),(1655,none),(1656,none),(1657,none),(1658,none),(1659,none),(1660,none),(1661,none),(1662,none),(1663,none),(1664,none),(1665,none),(1666,none),(1667,none),(1668,none),(1669,none),(1670,none),(1671,none),(1672,none),(1673,none),(1674,none),(1675,none),(1676,none),(1677,none),(1678,none),(1679,none),(1680,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step02.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain1_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step02.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step02.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain1_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain1_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step02

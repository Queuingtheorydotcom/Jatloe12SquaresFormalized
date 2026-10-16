import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step08
import Compact.HistoricalCommon.C701.Step08Groups00
import Compact.HistoricalCommon.C701.Step08Groups01
import Compact.HistoricalCommon.C701.Step08Groups02
import Compact.HistoricalCommon.C701.Step08Groups03
import Compact.HistoricalCommon.C701.Step08Groups04
import Compact.HistoricalCommon.C701.Step08Groups05
import Compact.HistoricalCommon.C701.Step08Groups06
import Compact.HistoricalCommon.C701.Step08Groups07
import Compact.HistoricalCommon.C701.Step08Groups08

namespace N12Compact.HistoricalCommon.C701.Step08
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 9 (.neighborCut 16 .leaf (.sourceCut 4 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))))) (.neighborCut 8 (.sourceCut 2 .leaf .leaf) (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 2 .leaf .leaf) (.neighborCut 8 .leaf .leaf)))))) (.sourceCut 10 (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 32 (.sourceCut 9 (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 4 .leaf .leaf) .leaf)) .leaf) (.neighborCut 16 (.sourceCut 9 .leaf (.sourceCut 5 (.neighborCut 8 .leaf .leaf) (.sourceCut 2 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf)))) (.neighborCut 4 (.sourceCut 9 .leaf (.sourceCut 5 .leaf .leaf)) (.neighborCut 4 .leaf .leaf))))))

theorem partition_checked : partition.Check ⟨0,38,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 38) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 38) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1688_header,context1691_header,context1693_header,context1694_header,context1695_header,context1696_header,context1697_header,context1608_header,context1661_header,context1662_header,context1663_header,context1664_header,context1665_header,context1666_header,context1667_header,context1668_header,context1669_header,context1670_header,context1671_header,context1672_header,context1673_header,context1674_header,context1675_header,context1676_header,context1677_header,context1678_header,context1679_header,context1680_header,context1681_header,context1682_header,context1683_header,context1684_header,context1685_header,context1686_header,context1687_header,context1689_header,context1690_header,context1692_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 38).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1525,none),(1526,none),(1527,none),(1528,some (fanBlockRows 641)),(1529,some (fanBlockRows 644)),(1530,some (fanBlockRows 646)),(1531,some (fanBlockRows 59)),(1532,some (fanBlockRows 59)),(1533,some (fanBlockRows 59)),(1534,some (fanBlockRows 59)),(1535,some (fanBlockRows 59)),(1536,some (fanBlockRows 59)),(1537,some (fanBlockRows 59)),(1538,some (fanBlockRows 616)),(1539,some (fanBlockRows 617)),(1540,some (fanBlockRows 618)),(1541,some (fanBlockRows 619)),(1542,some (fanBlockRows 620)),(1543,some (fanBlockRows 621)),(1544,some (fanBlockRows 622)),(1545,some (fanBlockRows 623)),(1546,some (fanBlockRows 624)),(1547,some (fanBlockRows 625)),(1548,some (fanBlockRows 626)),(1549,some (fanBlockRows 627)),(1550,some (fanBlockRows 628)),(1551,some (fanBlockRows 629)),(1552,some (fanBlockRows 630)),(1553,some (fanBlockRows 631)),(1554,some (fanBlockRows 632)),(1555,some (fanBlockRows 633)),(1556,some (fanBlockRows 634)),(1557,some (fanBlockRows 635)),(1558,some (fanBlockRows 636)),(1559,some (fanBlockRows 637)),(1560,some (fanBlockRows 638)),(1561,some (fanBlockRows 639)),(1562,some (fanBlockRows 640)),(1563,none),(1564,none),(1565,none),(1566,none),(1567,none),(1568,none),(1569,none),(1570,none),(1571,none),(1572,none),(1573,some (fanBlockRows 642)),(1574,some (fanBlockRows 643)),(1575,some (fanBlockRows 645)),(1576,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step08.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain11_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step08.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step08.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain11_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain11_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step08

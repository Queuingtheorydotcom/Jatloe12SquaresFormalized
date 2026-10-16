import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step07
import Compact.HistoricalCommon.C701.Step07Groups00
import Compact.HistoricalCommon.C701.Step07Groups01
import Compact.HistoricalCommon.C701.Step07Groups02
import Compact.HistoricalCommon.C701.Step07Groups03
import Compact.HistoricalCommon.C701.Step07Groups04
import Compact.HistoricalCommon.C701.Step07Groups05

namespace N12Compact.HistoricalCommon.C701.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 3 (.sourceCut 16 .leaf (.neighborCut 1 .leaf .leaf)) (.neighborCut 3 .leaf (.neighborCut 7 .leaf (.neighborCut 13 .leaf (.sourceCut 8 (.neighborCut 13 .leaf (.neighborCut 6 (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)) .leaf)) (.sourceCut 8 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf .leaf)))) (.neighborCut 13 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 4 .leaf (.sourceCut 4 .leaf .leaf))))))))))))

theorem partition_checked : partition.Check ⟨0,32,0,52⟩ scopes := by decide +kernel

theorem covered (i : Fin 32) (j : Fin 52) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 32) (j : Fin 52) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1596_header,context1601_header,context1602_header,context1603_header,context1604_header,context1605_header,context1606_header,context1607_header,context1524_header,context1577_header,context1578_header,context1579_header,context1580_header,context1581_header,context1582_header,context1583_header,context1584_header,context1585_header,context1586_header,context1587_header,context1588_header,context1589_header,context1590_header,context1591_header,context1592_header,context1593_header,context1594_header,context1595_header,context1597_header,context1598_header,context1599_header,context1600_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 32).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1473,none),(1474,none),(1475,some (fanBlockRows 604)),(1476,some (fanBlockRows 609)),(1477,some (fanBlockRows 610)),(1478,some (fanBlockRows 611)),(1479,some (fanBlockRows 612)),(1480,some (fanBlockRows 613)),(1481,some (fanBlockRows 614)),(1482,some (fanBlockRows 615)),(1483,some (fanBlockRows 584)),(1484,some (fanBlockRows 585)),(1485,some (fanBlockRows 586)),(1486,some (fanBlockRows 587)),(1487,some (fanBlockRows 588)),(1488,some (fanBlockRows 589)),(1489,some (fanBlockRows 590)),(1490,some (fanBlockRows 591)),(1491,some (fanBlockRows 592)),(1492,some (fanBlockRows 593)),(1493,some (fanBlockRows 594)),(1494,some (fanBlockRows 595)),(1495,some (fanBlockRows 596)),(1496,some (fanBlockRows 597)),(1497,some (fanBlockRows 598)),(1498,some (fanBlockRows 599)),(1499,some (fanBlockRows 600)),(1500,some (fanBlockRows 601)),(1501,some (fanBlockRows 602)),(1502,some (fanBlockRows 603)),(1503,some (fanBlockRows 605)),(1504,some (fanBlockRows 606)),(1505,some (fanBlockRows 607)),(1506,some (fanBlockRows 608)),(1507,none),(1508,none),(1509,none),(1510,none),(1511,none),(1512,none),(1513,none),(1514,none),(1515,none),(1516,none),(1517,none),(1518,none),(1519,none),(1520,none),(1521,none),(1522,none),(1523,none),(1524,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step07.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 52).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain10_6Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step07.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step07.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain10_6Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain10_6Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step07

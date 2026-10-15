import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step03
import Compact.HistoricalCommon.C978.Step03Groups00
import Compact.HistoricalCommon.C978.Step03Groups01
import Compact.HistoricalCommon.C978.Step03Groups02
import Compact.HistoricalCommon.C978.Step03Groups03

namespace N12Compact.HistoricalCommon.C978.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 7 (.neighborCut 6 (.sourceCut 3 (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf)) (.sourceCut 2 .leaf .leaf)) .leaf) (.sourceCut 1 .leaf (.sourceCut 2 .leaf (.sourceCut 4 .leaf (.sourceCut 15 .leaf (.sourceCut 15 .leaf (.neighborCut 6 (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf)) .leaf)))))))

theorem partition_checked : partition.Check ⟨0,59,0,12⟩ scopes := by decide +kernel

theorem covered (i : Fin 59) (j : Fin 12) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 59) (j : Fin 12) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9449_header,context9450_header,context9451_header,context9452_header,context9453_header,context9457_header,context9458_header,context9459_header,context9460_header,context9461_header,context427_header,context429_header,context431_header,context433_header,context435_header,context437_header,context439_header,context441_header,context443_header,context445_header,context447_header,context449_header,context451_header,context453_header,context455_header,context457_header,context459_header,context461_header,context463_header,context465_header,context467_header,context469_header,context471_header,context473_header,context475_header,context477_header,context479_header,context481_header,context483_header,context485_header,context487_header,context489_header,context491_header,context493_header,context495_header,context497_header,context499_header,context501_header,context503_header,context505_header,context507_header,context509_header,context511_header,context513_header,context515_header,context517_header,context9454_header,context9455_header,context9456_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 59).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1622,some (fanBlockRows 3901)),(1623,some (fanBlockRows 3902)),(1624,some (fanBlockRows 3903)),(1625,some (fanBlockRows 3904)),(1626,some (fanBlockRows 3905)),(1627,some (fanBlockRows 3909)),(1628,some (fanBlockRows 3910)),(1629,some (fanBlockRows 3911)),(1630,some (fanBlockRows 3912)),(1631,some (fanBlockRows 3913)),(1632,some (fanBlockRows 59)),(1633,some (fanBlockRows 59)),(1634,some (fanBlockRows 59)),(1635,some (fanBlockRows 59)),(1636,some (fanBlockRows 59)),(1637,some (fanBlockRows 59)),(1638,some (fanBlockRows 59)),(1639,some (fanBlockRows 59)),(1640,some (fanBlockRows 59)),(1641,some (fanBlockRows 59)),(1642,some (fanBlockRows 59)),(1643,some (fanBlockRows 59)),(1644,some (fanBlockRows 59)),(1645,some (fanBlockRows 59)),(1646,some (fanBlockRows 59)),(1647,some (fanBlockRows 59)),(1648,some (fanBlockRows 59)),(1649,some (fanBlockRows 59)),(1650,some (fanBlockRows 59)),(1651,some (fanBlockRows 59)),(1652,some (fanBlockRows 59)),(1653,some (fanBlockRows 59)),(1654,some (fanBlockRows 59)),(1655,some (fanBlockRows 59)),(1656,some (fanBlockRows 59)),(1657,some (fanBlockRows 59)),(1658,some (fanBlockRows 59)),(1659,some (fanBlockRows 59)),(1660,some (fanBlockRows 59)),(1661,some (fanBlockRows 59)),(1662,some (fanBlockRows 59)),(1663,some (fanBlockRows 59)),(1664,some (fanBlockRows 59)),(1665,some (fanBlockRows 59)),(1666,some (fanBlockRows 59)),(1667,some (fanBlockRows 59)),(1668,some (fanBlockRows 59)),(1669,some (fanBlockRows 59)),(1670,some (fanBlockRows 59)),(1671,some (fanBlockRows 59)),(1672,some (fanBlockRows 59)),(1673,some (fanBlockRows 59)),(1674,some (fanBlockRows 59)),(1675,some (fanBlockRows 59)),(1676,some (fanBlockRows 59)),(1677,some (fanBlockRows 59)),(1678,some (fanBlockRows 3906)),(1679,some (fanBlockRows 3907)),(1680,some (fanBlockRows 3908))]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step03.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 12).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain7_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step03.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step03.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain7_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain7_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step03

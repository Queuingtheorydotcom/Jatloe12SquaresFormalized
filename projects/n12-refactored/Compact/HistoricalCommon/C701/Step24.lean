import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step24
import Compact.HistoricalCommon.C701.Step24Groups00
import Compact.HistoricalCommon.C701.Step24Groups01
import Compact.HistoricalCommon.C701.Step24Groups02
import Compact.HistoricalCommon.C701.Step24Groups03
import Compact.HistoricalCommon.C701.Step24Groups04
import Compact.HistoricalCommon.C701.Step24Groups05
import Compact.HistoricalCommon.C701.Step24Groups06
import Compact.HistoricalCommon.C701.Step24Groups07
import Compact.HistoricalCommon.C701.Step24Groups08
import Compact.HistoricalCommon.C701.Step24Groups09
import Compact.HistoricalCommon.C701.Step24Groups10

namespace N12Compact.HistoricalCommon.C701.Step24
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 3 (.neighborCut 2 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf .leaf))) (.sourceCut 4 (.neighborCut 4 .leaf .leaf) (.sourceCut 3 (.neighborCut 2 .leaf (.neighborCut 2 (.sourceCut 1 .leaf .leaf) .leaf)) (.sourceCut 4 (.neighborCut 4 .leaf (.sourceCut 2 (.neighborCut 2 .leaf .leaf) .leaf)) (.sourceCut 15 (.neighborCut 4 .leaf (.neighborCut 2 .leaf (.neighborCut 1 (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf)) .leaf))) (.sourceCut 3 .leaf (.sourceCut 4 (.neighborCut 4 (.sourceCut 2 .leaf .leaf) (.neighborCut 2 .leaf .leaf)) (.sourceCut 8 (.neighborCut 4 (.sourceCut 4 (.neighborCut 2 .leaf .leaf) .leaf) (.neighborCut 2 .leaf .leaf)) (.sourceCut 7 (.neighborCut 4 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf))) (.neighborCut 4 (.sourceCut 4 .leaf (.sourceCut 2 .leaf (.neighborCut 2 .leaf .leaf))) (.neighborCut 2 .leaf (.sourceCut 4 (.neighborCut 1 .leaf .leaf) .leaf))))))))))))

theorem partition_checked : partition.Check ⟨0,59,0,9⟩ scopes := by decide +kernel

theorem covered (i : Fin 59) (j : Fin 9) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 59) (j : Fin 9) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1030_header,context1040_header,context1041_header,context1049_header,context1060_header,context1070_header,context1071_header,context1072_header,context1073_header,context425_header,context427_header,context429_header,context431_header,context433_header,context435_header,context437_header,context439_header,context441_header,context443_header,context445_header,context447_header,context449_header,context451_header,context453_header,context455_header,context457_header,context459_header,context461_header,context463_header,context465_header,context467_header,context469_header,context471_header,context1042_header,context1043_header,context1044_header,context1045_header,context1046_header,context1047_header,context1048_header,context1050_header,context1051_header,context1052_header,context1053_header,context1054_header,context1055_header,context1056_header,context1057_header,context1058_header,context1059_header,context1061_header,context1062_header,context1063_header,context1064_header,context1065_header,context1066_header,context1067_header,context1068_header,context1069_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 59).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1622,some (fanBlockRows 415)),(1623,some (fanBlockRows 416)),(1624,some (fanBlockRows 417)),(1625,some (fanBlockRows 425)),(1626,some (fanBlockRows 436)),(1627,some (fanBlockRows 446)),(1628,some (fanBlockRows 447)),(1629,some (fanBlockRows 448)),(1630,some (fanBlockRows 449)),(1631,some (fanBlockRows 59)),(1632,some (fanBlockRows 59)),(1633,some (fanBlockRows 59)),(1634,some (fanBlockRows 59)),(1635,some (fanBlockRows 59)),(1636,some (fanBlockRows 59)),(1637,some (fanBlockRows 59)),(1638,some (fanBlockRows 59)),(1639,some (fanBlockRows 59)),(1640,some (fanBlockRows 59)),(1641,some (fanBlockRows 59)),(1642,some (fanBlockRows 59)),(1643,some (fanBlockRows 59)),(1644,some (fanBlockRows 59)),(1645,some (fanBlockRows 59)),(1646,some (fanBlockRows 59)),(1647,some (fanBlockRows 59)),(1648,some (fanBlockRows 59)),(1649,some (fanBlockRows 59)),(1650,some (fanBlockRows 59)),(1651,some (fanBlockRows 59)),(1652,some (fanBlockRows 59)),(1653,some (fanBlockRows 59)),(1654,some (fanBlockRows 59)),(1655,some (fanBlockRows 418)),(1656,some (fanBlockRows 419)),(1657,some (fanBlockRows 420)),(1658,some (fanBlockRows 421)),(1659,some (fanBlockRows 422)),(1660,some (fanBlockRows 423)),(1661,some (fanBlockRows 424)),(1662,some (fanBlockRows 426)),(1663,some (fanBlockRows 427)),(1664,some (fanBlockRows 428)),(1665,some (fanBlockRows 429)),(1666,some (fanBlockRows 430)),(1667,some (fanBlockRows 431)),(1668,some (fanBlockRows 432)),(1669,some (fanBlockRows 433)),(1670,some (fanBlockRows 434)),(1671,some (fanBlockRows 435)),(1672,some (fanBlockRows 437)),(1673,some (fanBlockRows 438)),(1674,some (fanBlockRows 439)),(1675,some (fanBlockRows 440)),(1676,some (fanBlockRows 441)),(1677,some (fanBlockRows 442)),(1678,some (fanBlockRows 443)),(1679,some (fanBlockRows 444)),(1680,some (fanBlockRows 445))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step24.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 9).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain1_22Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step24.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step24.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain1_22Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain1_22Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step24

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step05
import Compact.HistoricalCommon.C701.Step05Groups00
import Compact.HistoricalCommon.C701.Step05Groups01
import Compact.HistoricalCommon.C701.Step05Groups02
import Compact.HistoricalCommon.C701.Step05Groups03
import Compact.HistoricalCommon.C701.Step05Groups04
import Compact.HistoricalCommon.C701.Step05Groups05
import Compact.HistoricalCommon.C701.Step05Groups06
import Compact.HistoricalCommon.C701.Step05Groups07
import Compact.HistoricalCommon.C701.Step05Groups08
import Compact.HistoricalCommon.C701.Step05Groups09
import Compact.HistoricalCommon.C701.Step05Groups10
import Compact.HistoricalCommon.C701.Step05Groups11

namespace N12Compact.HistoricalCommon.C701.Step05
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 13 (.neighborCut 6 (.sourceCut 6 .leaf .leaf) (.neighborCut 6 (.sourceCut 6 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf)))))) (.sourceCut 13 (.neighborCut 12 (.sourceCut 3 (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf)) (.sourceCut 3 .leaf (.sourceCut 3 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf))))) (.neighborCut 6 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf))))) (.sourceCut 6 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 6 (.sourceCut 3 .leaf (.neighborCut 3 .leaf .leaf)) .leaf)))) (.sourceCut 7 (.neighborCut 12 .leaf .leaf) (.sourceCut 6 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 6 (.sourceCut 3 .leaf (.neighborCut 3 .leaf .leaf)) .leaf)))) (.neighborCut 6 .leaf (.neighborCut 6 .leaf (.neighborCut 6 .leaf (.sourceCut 3 .leaf (.neighborCut 3 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,52,0,25⟩ scopes := by decide +kernel

theorem covered (i : Fin 52) (j : Fin 25) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 52) (j : Fin 25) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1520_header,context1521_header,context1522_header,context1523_header,context1479_header,context1480_header,context1481_header,context1482_header,context1483_header,context1484_header,context1485_header,context1486_header,context1487_header,context1488_header,context1489_header,context1490_header,context1387_header,context1389_header,context1391_header,context1393_header,context1395_header,context1397_header,context1399_header,context1491_header,context1492_header,context1493_header,context1494_header,context1495_header,context1496_header,context1497_header,context1498_header,context1499_header,context1500_header,context1501_header,context1502_header,context1503_header,context1504_header,context1505_header,context1506_header,context1507_header,context1508_header,context1509_header,context1510_header,context1511_header,context1512_header,context1513_header,context1514_header,context1515_header,context1516_header,context1517_header,context1518_header,context1519_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 52).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(203,none),(204,none),(205,none),(206,none),(207,none),(208,none),(209,some (fanBlockRows 580)),(210,some (fanBlockRows 581)),(211,some (fanBlockRows 582)),(212,some (fanBlockRows 583)),(213,some (fanBlockRows 539)),(214,some (fanBlockRows 540)),(215,some (fanBlockRows 541)),(216,some (fanBlockRows 542)),(217,some (fanBlockRows 543)),(218,some (fanBlockRows 544)),(219,some (fanBlockRows 545)),(220,some (fanBlockRows 546)),(221,some (fanBlockRows 547)),(222,some (fanBlockRows 548)),(223,some (fanBlockRows 549)),(224,some (fanBlockRows 550)),(225,some (fanBlockRows 59)),(226,some (fanBlockRows 59)),(227,some (fanBlockRows 59)),(228,some (fanBlockRows 59)),(229,some (fanBlockRows 59)),(230,some (fanBlockRows 59)),(231,some (fanBlockRows 59)),(232,some (fanBlockRows 551)),(233,some (fanBlockRows 552)),(234,some (fanBlockRows 553)),(235,some (fanBlockRows 554)),(236,some (fanBlockRows 555)),(237,some (fanBlockRows 556)),(238,some (fanBlockRows 557)),(239,some (fanBlockRows 558)),(240,some (fanBlockRows 559)),(241,some (fanBlockRows 560)),(242,some (fanBlockRows 561)),(243,some (fanBlockRows 562)),(244,some (fanBlockRows 563)),(245,some (fanBlockRows 564)),(246,some (fanBlockRows 565)),(247,some (fanBlockRows 566)),(248,some (fanBlockRows 567)),(249,some (fanBlockRows 568)),(250,some (fanBlockRows 569)),(251,some (fanBlockRows 570)),(252,some (fanBlockRows 571)),(253,some (fanBlockRows 572)),(254,some (fanBlockRows 573)),(255,some (fanBlockRows 574)),(256,some (fanBlockRows 575)),(257,some (fanBlockRows 576)),(258,some (fanBlockRows 577)),(259,some (fanBlockRows 578)),(260,some (fanBlockRows 579)),(261,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step05.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 25).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain2_5Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step05.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step05.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain2_5Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain2_5Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step05

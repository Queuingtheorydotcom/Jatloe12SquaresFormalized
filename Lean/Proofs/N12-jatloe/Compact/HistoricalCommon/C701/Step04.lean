import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step04
import Compact.HistoricalCommon.C701.Step04Groups00
import Compact.HistoricalCommon.C701.Step04Groups01
import Compact.HistoricalCommon.C701.Step04Groups02
import Compact.HistoricalCommon.C701.Step04Groups03
import Compact.HistoricalCommon.C701.Step04Groups04
import Compact.HistoricalCommon.C701.Step04Groups05
import Compact.HistoricalCommon.C701.Step04Groups06

namespace N12Compact.HistoricalCommon.C701.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 25 (.neighborCut 29 (.sourceCut 12 (.neighborCut 7 .leaf (.neighborCut 7 (.sourceCut 6 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf)))) .leaf) .leaf) (.neighborCut 7 (.sourceCut 12 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 7 (.sourceCut 12 .leaf .leaf) (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 15 .leaf (.sourceCut 12 (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf)) (.sourceCut 6 (.neighborCut 7 .leaf .leaf) (.neighborCut 7 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,50,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 50) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 50) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1363_header,context1440_header,context1451_header,context1462_header,context1473_header,context1474_header,context1475_header,context1476_header,context1477_header,context1478_header,context1430_header,context1431_header,context1432_header,context1433_header,context1434_header,context1435_header,context1436_header,context1437_header,context1438_header,context1439_header,context1441_header,context1442_header,context1443_header,context1444_header,context1445_header,context1446_header,context1447_header,context1448_header,context1449_header,context1450_header,context1452_header,context1453_header,context1454_header,context1455_header,context1456_header,context1457_header,context1458_header,context1459_header,context1460_header,context1461_header,context1463_header,context1464_header,context1465_header,context1466_header,context1467_header,context1468_header,context1469_header,context1470_header,context1471_header,context1472_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 50).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(804,some (fanBlockRows 514)),(805,some (fanBlockRows 515)),(806,some (fanBlockRows 516)),(807,some (fanBlockRows 523)),(808,some (fanBlockRows 534)),(809,some (fanBlockRows 535)),(810,some (fanBlockRows 536)),(811,some (fanBlockRows 537)),(812,some (fanBlockRows 538)),(813,some (fanBlockRows 59)),(814,some (fanBlockRows 59)),(815,some (fanBlockRows 59)),(816,some (fanBlockRows 59)),(817,some (fanBlockRows 59)),(818,some (fanBlockRows 59)),(819,some (fanBlockRows 59)),(820,some (fanBlockRows 59)),(821,some (fanBlockRows 59)),(822,some (fanBlockRows 59)),(823,some (fanBlockRows 59)),(824,some (fanBlockRows 59)),(825,some (fanBlockRows 59)),(826,some (fanBlockRows 59)),(827,some (fanBlockRows 59)),(828,some (fanBlockRows 59)),(829,some (fanBlockRows 59)),(830,some (fanBlockRows 59)),(831,some (fanBlockRows 59)),(832,some (fanBlockRows 59)),(833,some (fanBlockRows 59)),(834,some (fanBlockRows 59)),(835,some (fanBlockRows 59)),(836,some (fanBlockRows 59)),(837,some (fanBlockRows 59)),(838,some (fanBlockRows 517)),(839,some (fanBlockRows 518)),(840,some (fanBlockRows 519)),(841,some (fanBlockRows 520)),(842,some (fanBlockRows 521)),(843,some (fanBlockRows 522)),(844,some (fanBlockRows 524)),(845,some (fanBlockRows 525)),(846,some (fanBlockRows 526)),(847,some (fanBlockRows 527)),(848,some (fanBlockRows 528)),(849,some (fanBlockRows 529)),(850,some (fanBlockRows 530)),(851,some (fanBlockRows 531)),(852,some (fanBlockRows 532)),(853,some (fanBlockRows 533))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step04.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step04.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step04.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step04

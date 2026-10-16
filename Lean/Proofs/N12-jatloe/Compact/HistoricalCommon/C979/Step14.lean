import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step14
import Compact.HistoricalCommon.C979.Step14Groups00
import Compact.HistoricalCommon.C979.Step14Groups01
import Compact.HistoricalCommon.C979.Step14Groups02
import Compact.HistoricalCommon.C979.Step14Groups03
import Compact.HistoricalCommon.C979.Step14Groups04
import Compact.HistoricalCommon.C979.Step14Groups05
import Compact.HistoricalCommon.C979.Step14Groups06
import Compact.HistoricalCommon.C979.Step14Groups07
import Compact.HistoricalCommon.C979.Step14Groups08
import Compact.HistoricalCommon.C979.Step14Groups09

namespace N12Compact.HistoricalCommon.C979.Step14
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 15 (.sourceCut 18 .leaf (.sourceCut 19 (.neighborCut 7 .leaf .leaf) (.sourceCut 19 (.neighborCut 7 .leaf .leaf) (.sourceCut 9 .leaf (.neighborCut 7 .leaf .leaf))))) (.neighborCut 15 .leaf (.neighborCut 31 .leaf (.sourceCut 37 (.neighborCut 15 (.sourceCut 9 .leaf (.sourceCut 9 (.neighborCut 7 .leaf .leaf) (.neighborCut 7 .leaf (.neighborCut 4 .leaf .leaf)))) (.neighborCut 16 (.sourceCut 18 .leaf .leaf) (.neighborCut 15 .leaf (.neighborCut 8 .leaf (.sourceCut 18 .leaf (.neighborCut 4 .leaf .leaf)))))) (.neighborCut 7 (.sourceCut 19 .leaf .leaf) (.neighborCut 4 (.sourceCut 19 .leaf .leaf) (.neighborCut 4 (.sourceCut 19 .leaf .leaf) (.neighborCut 16 (.sourceCut 19 (.neighborCut 8 .leaf .leaf) (.sourceCut 9 .leaf .leaf)) (.neighborCut 15 .leaf (.neighborCut 8 .leaf (.sourceCut 19 (.neighborCut 4 .leaf .leaf) .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,75,0,123⟩ scopes := by decide +kernel

theorem covered (i : Fin 75) (j : Fin 123) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 75) (j : Fin 123) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context10439_header,context10563_header,context10564_header,context10565_header,context10566_header,context10567_header,context10568_header,context10569_header,context10570_header,context10571_header,context10572_header,context10573_header,context10574_header,context10575_header,context10576_header,context10577_header,context10578_header,context10579_header,context10580_header,context10581_header,context10582_header,context10583_header,context10584_header,context10585_header,context10586_header,context10587_header,context10588_header,context10589_header,context10590_header,context10591_header,context10592_header,context10593_header,context10594_header,context10595_header,context10596_header,context10597_header,context10598_header,context10599_header,context10600_header,context10601_header,context10602_header,context10603_header,context10604_header,context10605_header,context10606_header,context10607_header,context10608_header,context10609_header,context10610_header,context10611_header,context10612_header,context10613_header,context10614_header,context10615_header,context10616_header,context10617_header,context10618_header,context10619_header,context10620_header,context10621_header,context10622_header,context10623_header,context10624_header,context10625_header,context10626_header,context10627_header,context10628_header,context10629_header,context10630_header,context10631_header,context10632_header,context10633_header,context10634_header,context10635_header,context10636_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 75).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11621,none),(11622,none),(11623,none),(11624,none),(11625,none),(11626,none),(11627,none),(11628,none),(11629,none),(11630,none),(11631,none),(11632,none),(11633,none),(11634,none),(11635,none),(11636,none),(11637,none),(11638,some (fanBlockRows 4457)),(11639,some (fanBlockRows 4458)),(11640,some (fanBlockRows 4459)),(11641,some (fanBlockRows 4460)),(11642,some (fanBlockRows 4461)),(11643,some (fanBlockRows 4462)),(11644,some (fanBlockRows 59)),(11645,some (fanBlockRows 59)),(11646,some (fanBlockRows 4463)),(11647,some (fanBlockRows 4464)),(11648,some (fanBlockRows 4465)),(11649,some (fanBlockRows 4466)),(11650,some (fanBlockRows 4467)),(11651,some (fanBlockRows 4468)),(11652,some (fanBlockRows 4469)),(11653,some (fanBlockRows 4470)),(11654,some (fanBlockRows 4471)),(11655,some (fanBlockRows 4472)),(11656,some (fanBlockRows 4473)),(11657,some (fanBlockRows 4474)),(11658,some (fanBlockRows 4475)),(11659,some (fanBlockRows 4476)),(11660,some (fanBlockRows 4477)),(11661,some (fanBlockRows 4478)),(11662,some (fanBlockRows 4479)),(11663,some (fanBlockRows 4480)),(11664,some (fanBlockRows 4481)),(11665,some (fanBlockRows 4482)),(11666,some (fanBlockRows 4483)),(11667,some (fanBlockRows 4484)),(11668,some (fanBlockRows 4485)),(11669,some (fanBlockRows 4486)),(11670,some (fanBlockRows 4487)),(11671,some (fanBlockRows 4488)),(11672,some (fanBlockRows 4489)),(11673,some (fanBlockRows 4490)),(11674,some (fanBlockRows 4491)),(11675,some (fanBlockRows 4492)),(11676,some (fanBlockRows 4493)),(11677,some (fanBlockRows 4494)),(11678,some (fanBlockRows 4495)),(11679,some (fanBlockRows 4496)),(11680,some (fanBlockRows 4497)),(11681,some (fanBlockRows 4498)),(11682,some (fanBlockRows 4499)),(11683,some (fanBlockRows 4500)),(11684,some (fanBlockRows 4501)),(11685,some (fanBlockRows 4502)),(11686,some (fanBlockRows 4503)),(11687,some (fanBlockRows 4504)),(11688,some (fanBlockRows 4505)),(11689,some (fanBlockRows 4506)),(11690,some (fanBlockRows 4507)),(11691,some (fanBlockRows 4508)),(11692,some (fanBlockRows 4509)),(11693,some (fanBlockRows 4510)),(11694,some (fanBlockRows 4511)),(11695,some (fanBlockRows 4512)),(11696,some (fanBlockRows 4513)),(11697,some (fanBlockRows 4514)),(11698,some (fanBlockRows 4515)),(11699,some (fanBlockRows 4516)),(11700,some (fanBlockRows 4517)),(11701,some (fanBlockRows 4518)),(11702,some (fanBlockRows 4519)),(11703,some (fanBlockRows 4520)),(11704,some (fanBlockRows 4521)),(11705,some (fanBlockRows 4522)),(11706,some (fanBlockRows 4523)),(11707,some (fanBlockRows 4524)),(11708,some (fanBlockRows 4525)),(11709,some (fanBlockRows 4526)),(11710,some (fanBlockRows 4527)),(11711,some (fanBlockRows 4528)),(11712,some (fanBlockRows 4529)),(11713,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step14.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 123).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain6_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step14.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step14.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain6_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain6_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step14

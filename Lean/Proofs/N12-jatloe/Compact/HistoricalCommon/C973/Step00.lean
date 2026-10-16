import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step00
import Compact.HistoricalCommon.C973.Step00Groups00
import Compact.HistoricalCommon.C973.Step00Groups01
import Compact.HistoricalCommon.C973.Step00Groups02
import Compact.HistoricalCommon.C973.Step00Groups03
import Compact.HistoricalCommon.C973.Step00Groups04
import Compact.HistoricalCommon.C973.Step00Groups05
import Compact.HistoricalCommon.C973.Step00Groups06
import Compact.HistoricalCommon.C973.Step00Groups07
import Compact.HistoricalCommon.C973.Step00Groups08

namespace N12Compact.HistoricalCommon.C973.Step00
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
  (.sourceCut 30 (.neighborCut 14 (.sourceCut 7 (.neighborCut 7 .leaf .leaf) (.sourceCut 8 .leaf .leaf)) (.neighborCut 7 (.sourceCut 15 (.neighborCut 3 .leaf .leaf) (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 8 (.sourceCut 15 .leaf .leaf) (.neighborCut 15 .leaf (.sourceCut 7 .leaf (.sourceCut 8 (.neighborCut 7 .leaf (.neighborCut 4 .leaf .leaf)) (.sourceCut 7 (.neighborCut 7 .leaf .leaf) (.neighborCut 7 (.sourceCut 4 .leaf .leaf) .leaf)))))))) (.neighborCut 7 (.sourceCut 7 .leaf (.sourceCut 8 .leaf (.neighborCut 3 .leaf .leaf))) (.neighborCut 7 (.sourceCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 8 .leaf .leaf))) (.neighborCut 15 .leaf (.neighborCut 15 .leaf (.sourceCut 15 .leaf (.sourceCut 8 .leaf (.neighborCut 7 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,61,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 61) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 61) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6564_header,context6575_header,context6586_header,context6597_header,context6608_header,context6611_header,context6612_header,context6613_header,context6614_header,context6554_header,context6555_header,context6556_header,context6557_header,context6558_header,context6559_header,context6560_header,context6561_header,context6562_header,context6563_header,context6565_header,context6566_header,context6567_header,context6568_header,context6569_header,context6570_header,context6571_header,context6572_header,context6573_header,context6574_header,context6576_header,context6577_header,context6578_header,context6579_header,context6580_header,context6581_header,context6582_header,context6583_header,context6584_header,context6585_header,context6587_header,context6588_header,context6589_header,context6590_header,context6591_header,context6592_header,context6593_header,context6594_header,context6595_header,context6596_header,context6598_header,context6599_header,context6600_header,context6601_header,context6602_header,context6603_header,context6604_header,context6605_header,context6606_header,context6607_header,context6609_header,context6610_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 61).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7350,none),(7351,some (fanBlockRows 2557)),(7352,some (fanBlockRows 2568)),(7353,some (fanBlockRows 2579)),(7354,some (fanBlockRows 2590)),(7355,some (fanBlockRows 2601)),(7356,some (fanBlockRows 2604)),(7357,some (fanBlockRows 2605)),(7358,some (fanBlockRows 2606)),(7359,some (fanBlockRows 2607)),(7360,some (fanBlockRows 2547)),(7361,some (fanBlockRows 2548)),(7362,some (fanBlockRows 2549)),(7363,some (fanBlockRows 2550)),(7364,some (fanBlockRows 2551)),(7365,some (fanBlockRows 2552)),(7366,some (fanBlockRows 2553)),(7367,some (fanBlockRows 2554)),(7368,some (fanBlockRows 2555)),(7369,some (fanBlockRows 2556)),(7370,some (fanBlockRows 2558)),(7371,some (fanBlockRows 2559)),(7372,some (fanBlockRows 2560)),(7373,some (fanBlockRows 2561)),(7374,some (fanBlockRows 2562)),(7375,some (fanBlockRows 2563)),(7376,some (fanBlockRows 2564)),(7377,some (fanBlockRows 2565)),(7378,some (fanBlockRows 2566)),(7379,some (fanBlockRows 2567)),(7380,some (fanBlockRows 2569)),(7381,some (fanBlockRows 2570)),(7382,some (fanBlockRows 2571)),(7383,some (fanBlockRows 2572)),(7384,some (fanBlockRows 2573)),(7385,some (fanBlockRows 2574)),(7386,some (fanBlockRows 2575)),(7387,some (fanBlockRows 2576)),(7388,some (fanBlockRows 2577)),(7389,some (fanBlockRows 2578)),(7390,some (fanBlockRows 2580)),(7391,some (fanBlockRows 2581)),(7392,some (fanBlockRows 2582)),(7393,some (fanBlockRows 2583)),(7394,some (fanBlockRows 2584)),(7395,some (fanBlockRows 2585)),(7396,some (fanBlockRows 2586)),(7397,some (fanBlockRows 2587)),(7398,some (fanBlockRows 2588)),(7399,some (fanBlockRows 2589)),(7400,some (fanBlockRows 2591)),(7401,some (fanBlockRows 2592)),(7402,some (fanBlockRows 2593)),(7403,some (fanBlockRows 2594)),(7404,some (fanBlockRows 2595)),(7405,some (fanBlockRows 2596)),(7406,some (fanBlockRows 2597)),(7407,some (fanBlockRows 2598)),(7408,some (fanBlockRows 2599)),(7409,some (fanBlockRows 2600)),(7410,some (fanBlockRows 2602)),(7411,some (fanBlockRows 2603)),(7412,none),(7413,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step00.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step00.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step00.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step00

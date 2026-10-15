import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step12
import Compact.HistoricalCommon.C973.Step12Groups00
import Compact.HistoricalCommon.C973.Step12Groups01
import Compact.HistoricalCommon.C973.Step12Groups02
import Compact.HistoricalCommon.C973.Step12Groups03
import Compact.HistoricalCommon.C973.Step12Groups04
import Compact.HistoricalCommon.C973.Step12Groups05
import Compact.HistoricalCommon.C973.Step12Groups06
import Compact.HistoricalCommon.C973.Step12Groups07
import Compact.HistoricalCommon.C973.Step12Groups08
import Compact.HistoricalCommon.C973.Step12Groups09

namespace N12Compact.HistoricalCommon.C973.Step12
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 8 .leaf (.neighborCut 4 .leaf .leaf))) (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf)) .leaf)))) (.sourceCut 16 (.neighborCut 32 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.sourceCut 4 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))) (.sourceCut 8 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)))) (.neighborCut 32 (.sourceCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))) (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 4 .leaf .leaf) .leaf))))))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6615_header,context6690_header,context6701_header,context6712_header,context6723_header,context6734_header,context6739_header,context6740_header,context6741_header,context6742_header,context6680_header,context6681_header,context6682_header,context6683_header,context6684_header,context6685_header,context6686_header,context6687_header,context6688_header,context6689_header,context6691_header,context6692_header,context6693_header,context6694_header,context6695_header,context6696_header,context6697_header,context6698_header,context6699_header,context6700_header,context6702_header,context6703_header,context6704_header,context6705_header,context6706_header,context6707_header,context6708_header,context6709_header,context6710_header,context6711_header,context6713_header,context6714_header,context6715_header,context6716_header,context6717_header,context6718_header,context6719_header,context6720_header,context6721_header,context6722_header,context6724_header,context6725_header,context6726_header,context6727_header,context6728_header,context6729_header,context6730_header,context6731_header,context6732_header,context6733_header,context6735_header,context6736_header,context6737_header,context6738_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6494,some (fanBlockRows 2608)),(6495,some (fanBlockRows 2619)),(6496,some (fanBlockRows 2630)),(6497,some (fanBlockRows 2641)),(6498,some (fanBlockRows 2652)),(6499,some (fanBlockRows 2663)),(6500,some (fanBlockRows 2668)),(6501,some (fanBlockRows 2669)),(6502,some (fanBlockRows 2670)),(6503,some (fanBlockRows 2671)),(6504,some (fanBlockRows 2609)),(6505,some (fanBlockRows 2610)),(6506,some (fanBlockRows 2611)),(6507,some (fanBlockRows 2612)),(6508,some (fanBlockRows 2613)),(6509,some (fanBlockRows 2614)),(6510,some (fanBlockRows 2615)),(6511,some (fanBlockRows 2616)),(6512,some (fanBlockRows 2617)),(6513,some (fanBlockRows 2618)),(6514,some (fanBlockRows 2620)),(6515,some (fanBlockRows 2621)),(6516,some (fanBlockRows 2622)),(6517,some (fanBlockRows 2623)),(6518,some (fanBlockRows 2624)),(6519,some (fanBlockRows 2625)),(6520,some (fanBlockRows 2626)),(6521,some (fanBlockRows 2627)),(6522,some (fanBlockRows 2628)),(6523,some (fanBlockRows 2629)),(6524,some (fanBlockRows 2631)),(6525,some (fanBlockRows 2632)),(6526,some (fanBlockRows 2633)),(6527,some (fanBlockRows 2634)),(6528,some (fanBlockRows 2635)),(6529,some (fanBlockRows 2636)),(6530,some (fanBlockRows 2637)),(6531,some (fanBlockRows 2638)),(6532,some (fanBlockRows 2639)),(6533,some (fanBlockRows 2640)),(6534,some (fanBlockRows 2642)),(6535,some (fanBlockRows 2643)),(6536,some (fanBlockRows 2644)),(6537,some (fanBlockRows 2645)),(6538,some (fanBlockRows 2646)),(6539,some (fanBlockRows 2647)),(6540,some (fanBlockRows 2648)),(6541,some (fanBlockRows 2649)),(6542,some (fanBlockRows 2650)),(6543,some (fanBlockRows 2651)),(6544,some (fanBlockRows 2653)),(6545,some (fanBlockRows 2654)),(6546,some (fanBlockRows 2655)),(6547,some (fanBlockRows 2656)),(6548,some (fanBlockRows 2657)),(6549,some (fanBlockRows 2658)),(6550,some (fanBlockRows 2659)),(6551,some (fanBlockRows 2660)),(6552,some (fanBlockRows 2661)),(6553,some (fanBlockRows 2662)),(6554,some (fanBlockRows 2664)),(6555,some (fanBlockRows 2665)),(6556,some (fanBlockRows 2666)),(6557,some (fanBlockRows 2667))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step12.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain7_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step12.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step12.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain7_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain7_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step12

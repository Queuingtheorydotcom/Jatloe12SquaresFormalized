import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step01
import Compact.HistoricalCommon.C978.Step01Groups00
import Compact.HistoricalCommon.C978.Step01Groups01
import Compact.HistoricalCommon.C978.Step01Groups02
import Compact.HistoricalCommon.C978.Step01Groups03
import Compact.HistoricalCommon.C978.Step01Groups04
import Compact.HistoricalCommon.C978.Step01Groups05
import Compact.HistoricalCommon.C978.Step01Groups06
import Compact.HistoricalCommon.C978.Step01Groups07
import Compact.HistoricalCommon.C978.Step01Groups08

namespace N12Compact.HistoricalCommon.C978.Step01
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 15 (.neighborCut 14 (.sourceCut 7 (.neighborCut 7 .leaf .leaf) .leaf) (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf .leaf)))) (.sourceCut 15 (.neighborCut 14 (.sourceCut 7 .leaf (.neighborCut 7 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 15 (.sourceCut 7 (.neighborCut 7 .leaf .leaf) .leaf) (.neighborCut 15 .leaf (.neighborCut 7 .leaf (.sourceCut 7 (.neighborCut 4 .leaf .leaf) .leaf))))) (.neighborCut 7 (.sourceCut 7 .leaf (.sourceCut 8 .leaf (.neighborCut 3 .leaf .leaf))) (.neighborCut 7 (.sourceCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 8 .leaf .leaf))) (.neighborCut 15 .leaf (.neighborCut 15 .leaf (.sourceCut 7 (.neighborCut 7 .leaf .leaf) (.sourceCut 8 .leaf (.neighborCut 7 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,61,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 61) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 61) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9270_header,context9281_header,context9292_header,context9303_header,context9314_header,context9317_header,context9318_header,context9319_header,context9320_header,context9260_header,context9261_header,context9262_header,context9263_header,context9264_header,context9265_header,context9266_header,context9267_header,context9268_header,context9269_header,context9271_header,context9272_header,context9273_header,context9274_header,context9275_header,context9276_header,context9277_header,context9278_header,context9279_header,context9280_header,context9282_header,context9283_header,context9284_header,context9285_header,context9286_header,context9287_header,context9288_header,context9289_header,context9290_header,context9291_header,context9293_header,context9294_header,context9295_header,context9296_header,context9297_header,context9298_header,context9299_header,context9300_header,context9301_header,context9302_header,context9304_header,context9305_header,context9306_header,context9307_header,context9308_header,context9309_header,context9310_header,context9311_header,context9312_header,context9313_header,context9315_header,context9316_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 61).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8463,none),(8464,some (fanBlockRows 2557)),(8465,some (fanBlockRows 2568)),(8466,some (fanBlockRows 2579)),(8467,some (fanBlockRows 2590)),(8468,some (fanBlockRows 2601)),(8469,some (fanBlockRows 2604)),(8470,some (fanBlockRows 2605)),(8471,some (fanBlockRows 3887)),(8472,some (fanBlockRows 3888)),(8473,some (fanBlockRows 3878)),(8474,some (fanBlockRows 3879)),(8475,some (fanBlockRows 3880)),(8476,some (fanBlockRows 3881)),(8477,some (fanBlockRows 3882)),(8478,some (fanBlockRows 3883)),(8479,some (fanBlockRows 3884)),(8480,some (fanBlockRows 2554)),(8481,some (fanBlockRows 2555)),(8482,some (fanBlockRows 2556)),(8483,some (fanBlockRows 2558)),(8484,some (fanBlockRows 2559)),(8485,some (fanBlockRows 2560)),(8486,some (fanBlockRows 2561)),(8487,some (fanBlockRows 2562)),(8488,some (fanBlockRows 2563)),(8489,some (fanBlockRows 2564)),(8490,some (fanBlockRows 2565)),(8491,some (fanBlockRows 2566)),(8492,some (fanBlockRows 2567)),(8493,some (fanBlockRows 2569)),(8494,some (fanBlockRows 2570)),(8495,some (fanBlockRows 2571)),(8496,some (fanBlockRows 2572)),(8497,some (fanBlockRows 2573)),(8498,some (fanBlockRows 2574)),(8499,some (fanBlockRows 2575)),(8500,some (fanBlockRows 2576)),(8501,some (fanBlockRows 2577)),(8502,some (fanBlockRows 2578)),(8503,some (fanBlockRows 2580)),(8504,some (fanBlockRows 2581)),(8505,some (fanBlockRows 2582)),(8506,some (fanBlockRows 2583)),(8507,some (fanBlockRows 2584)),(8508,some (fanBlockRows 2585)),(8509,some (fanBlockRows 3885)),(8510,some (fanBlockRows 3886)),(8511,some (fanBlockRows 2588)),(8512,some (fanBlockRows 2589)),(8513,some (fanBlockRows 2591)),(8514,some (fanBlockRows 2592)),(8515,some (fanBlockRows 2593)),(8516,some (fanBlockRows 2594)),(8517,some (fanBlockRows 2595)),(8518,some (fanBlockRows 2596)),(8519,some (fanBlockRows 2597)),(8520,some (fanBlockRows 2598)),(8521,some (fanBlockRows 2599)),(8522,some (fanBlockRows 2600)),(8523,some (fanBlockRows 2602)),(8524,some (fanBlockRows 2603)),(8525,none),(8526,none)]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step01.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain8_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step01.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step01.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain8_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain8_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step01

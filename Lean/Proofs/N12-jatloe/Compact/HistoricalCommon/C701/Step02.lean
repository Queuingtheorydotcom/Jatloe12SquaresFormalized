import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step02
import Compact.HistoricalCommon.C701.Step02Groups00
import Compact.HistoricalCommon.C701.Step02Groups01
import Compact.HistoricalCommon.C701.Step02Groups02
import Compact.HistoricalCommon.C701.Step02Groups03
import Compact.HistoricalCommon.C701.Step02Groups04
import Compact.HistoricalCommon.C701.Step02Groups05
import Compact.HistoricalCommon.C701.Step02Groups06
import Compact.HistoricalCommon.C701.Step02Groups07
import Compact.HistoricalCommon.C701.Step02Groups08
import Compact.HistoricalCommon.C701.Step02Groups09

namespace N12Compact.HistoricalCommon.C701.Step02
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
  (.neighborCut 7 (.sourceCut 6 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 6 .leaf (.sourceCut 7 (.neighborCut 3 .leaf .leaf) (.sourceCut 12 .leaf .leaf)))))) (.neighborCut 7 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.sourceCut 13 .leaf .leaf))) (.neighborCut 15 .leaf (.sourceCut 12 (.neighborCut 15 .leaf (.sourceCut 6 (.neighborCut 7 .leaf .leaf) (.sourceCut 3 (.neighborCut 7 .leaf .leaf) (.neighborCut 7 .leaf .leaf)))) (.sourceCut 6 (.neighborCut 15 .leaf .leaf) (.sourceCut 3 (.neighborCut 15 .leaf .leaf) (.sourceCut 4 (.neighborCut 15 .leaf .leaf) (.sourceCut 12 (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf (.neighborCut 8 .leaf .leaf)))) (.neighborCut 15 (.sourceCut 6 (.neighborCut 7 .leaf .leaf) .leaf) (.neighborCut 7 (.sourceCut 6 .leaf .leaf) .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,50,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 50) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 50) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8841_header,context8842_header,context8843_header,context8844_header,context8797_header,context8798_header,context8799_header,context8800_header,context8801_header,context8802_header,context8803_header,context8804_header,context8805_header,context8806_header,context8807_header,context8808_header,context8809_header,context8810_header,context8811_header,context8812_header,context8813_header,context8814_header,context7504_header,context7506_header,context8815_header,context8816_header,context8817_header,context8818_header,context8819_header,context8820_header,context8821_header,context8822_header,context8823_header,context8824_header,context8825_header,context8826_header,context8827_header,context8828_header,context8829_header,context8830_header,context8831_header,context8832_header,context8833_header,context8834_header,context8835_header,context8836_header,context8837_header,context8838_header,context8839_header,context8840_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 50).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(577,none),(578,none),(579,none),(580,none),(581,none),(582,none),(583,some (fanBlockRows 3714)),(584,some (fanBlockRows 3715)),(585,some (fanBlockRows 3716)),(586,some (fanBlockRows 3717)),(587,some (fanBlockRows 3687)),(588,some (fanBlockRows 3688)),(589,some (fanBlockRows 3689)),(590,some (fanBlockRows 3690)),(591,some (fanBlockRows 59)),(592,some (fanBlockRows 59)),(593,some (fanBlockRows 59)),(594,some (fanBlockRows 59)),(595,some (fanBlockRows 59)),(596,some (fanBlockRows 59)),(597,some (fanBlockRows 59)),(598,some (fanBlockRows 59)),(599,some (fanBlockRows 59)),(600,some (fanBlockRows 59)),(601,some (fanBlockRows 59)),(602,some (fanBlockRows 59)),(603,some (fanBlockRows 59)),(604,some (fanBlockRows 59)),(605,some (fanBlockRows 59)),(606,some (fanBlockRows 59)),(607,some (fanBlockRows 59)),(608,some (fanBlockRows 59)),(609,some (fanBlockRows 59)),(610,some (fanBlockRows 3691)),(611,some (fanBlockRows 3692)),(612,some (fanBlockRows 3693)),(613,some (fanBlockRows 3694)),(614,some (fanBlockRows 3695)),(615,some (fanBlockRows 3696)),(616,some (fanBlockRows 3697)),(617,some (fanBlockRows 3698)),(618,some (fanBlockRows 3699)),(619,some (fanBlockRows 3700)),(620,some (fanBlockRows 3701)),(621,some (fanBlockRows 3702)),(622,some (fanBlockRows 3703)),(623,some (fanBlockRows 3704)),(624,some (fanBlockRows 3705)),(625,some (fanBlockRows 3706)),(626,some (fanBlockRows 3707)),(627,some (fanBlockRows 3708)),(628,some (fanBlockRows 3709)),(629,some (fanBlockRows 3710)),(630,some (fanBlockRows 3711)),(631,some (fanBlockRows 3712)),(632,some (fanBlockRows 3713)),(633,none),(634,none),(635,none),(636,none),(637,none),(638,none),(639,none),(640,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step02.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain8_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step02.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step02.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain8_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain8_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step02

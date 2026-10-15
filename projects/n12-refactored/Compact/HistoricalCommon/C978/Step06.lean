import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step06
import Compact.HistoricalCommon.C978.Step06Groups00
import Compact.HistoricalCommon.C978.Step06Groups01
import Compact.HistoricalCommon.C978.Step06Groups02
import Compact.HistoricalCommon.C978.Step06Groups03
import Compact.HistoricalCommon.C978.Step06Groups04
import Compact.HistoricalCommon.C978.Step06Groups05
import Compact.HistoricalCommon.C978.Step06Groups06
import Compact.HistoricalCommon.C978.Step06Groups07

namespace N12Compact.HistoricalCommon.C978.Step06
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 6 (.neighborCut 6 .leaf (.sourceCut 3 .leaf (.sourceCut 1 .leaf .leaf))) (.sourceCut 3 (.neighborCut 3 .leaf (.neighborCut 3 (.sourceCut 1 .leaf .leaf) (.neighborCut 3 .leaf (.sourceCut 1 .leaf .leaf)))) (.sourceCut 4 (.neighborCut 6 (.sourceCut 2 .leaf .leaf) .leaf) (.sourceCut 7 .leaf (.sourceCut 7 .leaf (.sourceCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 3 .leaf (.sourceCut 4 (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 4 (.neighborCut 2 .leaf .leaf) (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))))))))))))))

theorem partition_checked : partition.Check ⟨0,55,0,13⟩ scopes := by decide +kernel

theorem covered (i : Fin 55) (j : Fin 13) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 55) (j : Fin 13) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9507_header,context9508_header,context9509_header,context9510_header,context9462_header,context9476_header,context9477_header,context9478_header,context8801_header,context8802_header,context8803_header,context8804_header,context8805_header,context8806_header,context8807_header,context8808_header,context8809_header,context8810_header,context8811_header,context8812_header,context8813_header,context8814_header,context7504_header,context7506_header,context8815_header,context8816_header,context8817_header,context9479_header,context9480_header,context9481_header,context9482_header,context9483_header,context9484_header,context9485_header,context9486_header,context9487_header,context9488_header,context9489_header,context9490_header,context9491_header,context9492_header,context9493_header,context9494_header,context9495_header,context9496_header,context9497_header,context9498_header,context9499_header,context9500_header,context9501_header,context9502_header,context9503_header,context9504_header,context9505_header,context9506_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 55).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(577,none),(578,none),(579,none),(580,none),(581,none),(582,none),(583,some (fanBlockRows 3934)),(584,some (fanBlockRows 3935)),(585,some (fanBlockRows 3936)),(586,some (fanBlockRows 3937)),(587,some (fanBlockRows 3914)),(588,some (fanBlockRows 3915)),(589,some (fanBlockRows 3916)),(590,some (fanBlockRows 3917)),(591,some (fanBlockRows 59)),(592,some (fanBlockRows 59)),(593,some (fanBlockRows 59)),(594,some (fanBlockRows 59)),(595,some (fanBlockRows 59)),(596,some (fanBlockRows 59)),(597,some (fanBlockRows 59)),(598,some (fanBlockRows 59)),(599,some (fanBlockRows 59)),(600,some (fanBlockRows 59)),(601,some (fanBlockRows 59)),(602,some (fanBlockRows 59)),(603,some (fanBlockRows 59)),(604,some (fanBlockRows 59)),(605,some (fanBlockRows 59)),(606,some (fanBlockRows 59)),(607,some (fanBlockRows 59)),(608,some (fanBlockRows 59)),(609,some (fanBlockRows 59)),(610,some (fanBlockRows 59)),(611,some (fanBlockRows 59)),(612,some (fanBlockRows 59)),(613,some (fanBlockRows 59)),(614,some (fanBlockRows 59)),(615,some (fanBlockRows 59)),(616,some (fanBlockRows 59)),(617,some (fanBlockRows 59)),(618,some (fanBlockRows 59)),(619,some (fanBlockRows 59)),(620,some (fanBlockRows 59)),(621,some (fanBlockRows 59)),(622,some (fanBlockRows 3918)),(623,some (fanBlockRows 3919)),(624,some (fanBlockRows 3920)),(625,some (fanBlockRows 3921)),(626,some (fanBlockRows 3922)),(627,some (fanBlockRows 3923)),(628,some (fanBlockRows 3924)),(629,some (fanBlockRows 3925)),(630,some (fanBlockRows 3926)),(631,some (fanBlockRows 3927)),(632,some (fanBlockRows 3928)),(633,some (fanBlockRows 3929)),(634,some (fanBlockRows 3930)),(635,some (fanBlockRows 3931)),(636,some (fanBlockRows 3932)),(637,some (fanBlockRows 3933)),(638,none),(639,none),(640,none)]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step06.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 13).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain8_4Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step06.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step06.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain8_4Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain8_4Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step06

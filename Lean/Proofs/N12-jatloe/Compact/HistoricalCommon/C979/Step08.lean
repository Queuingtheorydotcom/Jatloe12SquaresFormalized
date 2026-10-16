import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step08
import Compact.HistoricalCommon.C979.Step08Groups00
import Compact.HistoricalCommon.C979.Step08Groups01
import Compact.HistoricalCommon.C979.Step08Groups02
import Compact.HistoricalCommon.C979.Step08Groups03
import Compact.HistoricalCommon.C979.Step08Groups04
import Compact.HistoricalCommon.C979.Step08Groups05
import Compact.HistoricalCommon.C979.Step08Groups06

namespace N12Compact.HistoricalCommon.C979.Step08
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
  (.neighborCut 28 (.sourceCut 23 .leaf (.sourceCut 12 (.neighborCut 14 .leaf (.sourceCut 6 .leaf .leaf)) (.sourceCut 12 .leaf (.sourceCut 23 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf .leaf)))))) (.neighborCut 29 (.sourceCut 47 (.neighborCut 7 (.sourceCut 23 .leaf (.sourceCut 12 .leaf .leaf)) (.neighborCut 7 .leaf .leaf)) .leaf) (.neighborCut 28 .leaf (.sourceCut 47 (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.neighborCut 4 .leaf .leaf))) (.sourceCut 23 .leaf (.neighborCut 7 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,94,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 94) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 94) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context13149_header,context13160_header,context13069_header,context13070_header,context13071_header,context13072_header,context13073_header,context13074_header,context13075_header,context13076_header,context13077_header,context13078_header,context13079_header,context13080_header,context13081_header,context13082_header,context13083_header,context13084_header,context13085_header,context13086_header,context13087_header,context13088_header,context13089_header,context13090_header,context13091_header,context13092_header,context13093_header,context13094_header,context13095_header,context13096_header,context13097_header,context13098_header,context13099_header,context13100_header,context13101_header,context13102_header,context13103_header,context13104_header,context13105_header,context13106_header,context13107_header,context13108_header,context13109_header,context13110_header,context13111_header,context13112_header,context13113_header,context13114_header,context13115_header,context13116_header,context13117_header,context13118_header,context13119_header,context13120_header,context13121_header,context13122_header,context13123_header,context13124_header,context13125_header,context13126_header,context13127_header,context13128_header,context13129_header,context13130_header,context13131_header,context13132_header,context13133_header,context13134_header,context13135_header,context13136_header,context13137_header,context13138_header,context13139_header,context13140_header,context13141_header,context13142_header,context13143_header,context13144_header,context13145_header,context13146_header,context13147_header,context13148_header,context13150_header,context13151_header,context13152_header,context13153_header,context13154_header,context13155_header,context13156_header,context13157_header,context13158_header,context13159_header,context13067_header,context13068_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 94).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2067,none),(8625,none),(8626,none),(8627,none),(8628,none),(8629,none),(8630,none),(8631,none),(8632,some (fanBlockRows 798)),(8633,some (fanBlockRows 809)),(8634,some (fanBlockRows 711)),(8635,some (fanBlockRows 719)),(8636,some (fanBlockRows 720)),(8637,some (fanBlockRows 721)),(8638,some (fanBlockRows 722)),(8639,some (fanBlockRows 723)),(8640,some (fanBlockRows 724)),(8641,some (fanBlockRows 725)),(8642,some (fanBlockRows 726)),(8643,some (fanBlockRows 727)),(8644,some (fanBlockRows 728)),(8645,some (fanBlockRows 729)),(8646,some (fanBlockRows 730)),(8647,some (fanBlockRows 731)),(8648,some (fanBlockRows 732)),(8649,some (fanBlockRows 733)),(8650,some (fanBlockRows 734)),(8651,some (fanBlockRows 735)),(8652,some (fanBlockRows 736)),(8653,some (fanBlockRows 737)),(8654,some (fanBlockRows 5532)),(8655,some (fanBlockRows 5533)),(8656,some (fanBlockRows 5534)),(8657,some (fanBlockRows 5535)),(8658,some (fanBlockRows 59)),(8659,some (fanBlockRows 59)),(8660,some (fanBlockRows 59)),(8661,some (fanBlockRows 59)),(8662,some (fanBlockRows 59)),(8663,some (fanBlockRows 59)),(8664,some (fanBlockRows 59)),(8665,some (fanBlockRows 59)),(8666,some (fanBlockRows 59)),(8667,some (fanBlockRows 59)),(8668,some (fanBlockRows 59)),(8669,some (fanBlockRows 59)),(8670,some (fanBlockRows 59)),(8671,some (fanBlockRows 59)),(8672,some (fanBlockRows 59)),(8673,some (fanBlockRows 59)),(8674,some (fanBlockRows 59)),(8675,some (fanBlockRows 59)),(8676,some (fanBlockRows 59)),(8677,some (fanBlockRows 59)),(8678,some (fanBlockRows 59)),(8679,some (fanBlockRows 59)),(8680,some (fanBlockRows 59)),(8681,some (fanBlockRows 59)),(8682,some (fanBlockRows 59)),(8683,some (fanBlockRows 59)),(8684,some (fanBlockRows 59)),(8685,some (fanBlockRows 59)),(8686,some (fanBlockRows 59)),(8687,some (fanBlockRows 59)),(8688,some (fanBlockRows 59)),(8689,some (fanBlockRows 59)),(8690,some (fanBlockRows 59)),(8691,some (fanBlockRows 59)),(8692,some (fanBlockRows 59)),(8693,some (fanBlockRows 59)),(8694,some (fanBlockRows 59)),(8695,some (fanBlockRows 59)),(8696,some (fanBlockRows 59)),(8697,some (fanBlockRows 59)),(8698,some (fanBlockRows 59)),(8699,some (fanBlockRows 59)),(8700,some (fanBlockRows 59)),(8701,some (fanBlockRows 59)),(8702,some (fanBlockRows 59)),(8703,some (fanBlockRows 59)),(8704,some (fanBlockRows 5536)),(8705,some (fanBlockRows 5537)),(8706,some (fanBlockRows 5538)),(8707,some (fanBlockRows 5539)),(8708,some (fanBlockRows 5540)),(8709,some (fanBlockRows 701)),(8710,some (fanBlockRows 702)),(8711,some (fanBlockRows 703)),(8712,some (fanBlockRows 704)),(8713,some (fanBlockRows 705)),(8714,some (fanBlockRows 706)),(8715,some (fanBlockRows 707)),(8716,some (fanBlockRows 708)),(8717,some (fanBlockRows 709)),(8718,some (fanBlockRows 710)),(8719,some (fanBlockRows 712)),(8720,some (fanBlockRows 713)),(8721,some (fanBlockRows 714)),(8722,some (fanBlockRows 715)),(8723,some (fanBlockRows 716)),(8724,some (fanBlockRows 717)),(8725,some (fanBlockRows 718)),(8726,none),(8727,none),(8728,none),(8729,none),(8730,none),(8731,none),(8732,none),(8733,none),(8734,none),(8735,none),(2194,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step08.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step08.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step08.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step08

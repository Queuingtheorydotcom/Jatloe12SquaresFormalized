import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step07
import Compact.HistoricalCommon.C973.Step07Groups00
import Compact.HistoricalCommon.C973.Step07Groups01
import Compact.HistoricalCommon.C973.Step07Groups02
import Compact.HistoricalCommon.C973.Step07Groups03
import Compact.HistoricalCommon.C973.Step07Groups04
import Compact.HistoricalCommon.C973.Step07Groups05
import Compact.HistoricalCommon.C973.Step07Groups06
import Compact.HistoricalCommon.C973.Step07Groups07

namespace N12Compact.HistoricalCommon.C973.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 16 (.sourceCut 8 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)) .leaf)) (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 8 .leaf (.neighborCut 4 .leaf .leaf))) (.neighborCut 8 (.sourceCut 4 .leaf (.sourceCut 4 .leaf (.sourceCut 8 .leaf .leaf))) (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)))))) (.neighborCut 16 (.sourceCut 16 .leaf .leaf) (.neighborCut 8 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 8 (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)))))))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8517_header,context8592_header,context8603_header,context8614_header,context8625_header,context8636_header,context8641_header,context8642_header,context8643_header,context8644_header,context8582_header,context8583_header,context8584_header,context8585_header,context8586_header,context8587_header,context8588_header,context8589_header,context8590_header,context8591_header,context8593_header,context8594_header,context8595_header,context8596_header,context8597_header,context8598_header,context8599_header,context8600_header,context8601_header,context8602_header,context8604_header,context8605_header,context8606_header,context8607_header,context8608_header,context8609_header,context8610_header,context8611_header,context8612_header,context8613_header,context8615_header,context8616_header,context8617_header,context8618_header,context8619_header,context8620_header,context8621_header,context8622_header,context8623_header,context8624_header,context8626_header,context8627_header,context8628_header,context8629_header,context8630_header,context8631_header,context8632_header,context8633_header,context8634_header,context8635_header,context8637_header,context8638_header,context8639_header,context8640_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7222,some (fanBlockRows 3492)),(7223,some (fanBlockRows 3501)),(7224,some (fanBlockRows 3502)),(7225,some (fanBlockRows 3509)),(7226,some (fanBlockRows 3520)),(7227,some (fanBlockRows 3531)),(7228,some (fanBlockRows 3536)),(7229,some (fanBlockRows 3537)),(7230,some (fanBlockRows 3538)),(7231,some (fanBlockRows 3539)),(7232,some (fanBlockRows 3493)),(7233,some (fanBlockRows 3494)),(7234,some (fanBlockRows 3495)),(7235,some (fanBlockRows 3496)),(7236,some (fanBlockRows 3497)),(7237,some (fanBlockRows 3498)),(7238,some (fanBlockRows 3499)),(7239,some (fanBlockRows 3500)),(7240,some (fanBlockRows 592)),(7241,some (fanBlockRows 593)),(7242,some (fanBlockRows 594)),(7243,some (fanBlockRows 595)),(7244,some (fanBlockRows 596)),(7245,some (fanBlockRows 597)),(7246,some (fanBlockRows 598)),(7247,some (fanBlockRows 599)),(7248,some (fanBlockRows 600)),(7249,some (fanBlockRows 601)),(7250,some (fanBlockRows 602)),(7251,some (fanBlockRows 603)),(7252,some (fanBlockRows 605)),(7253,some (fanBlockRows 606)),(7254,some (fanBlockRows 607)),(7255,some (fanBlockRows 608)),(7256,some (fanBlockRows 3503)),(7257,some (fanBlockRows 3504)),(7258,some (fanBlockRows 3505)),(7259,some (fanBlockRows 3506)),(7260,some (fanBlockRows 3507)),(7261,some (fanBlockRows 3508)),(7262,some (fanBlockRows 3510)),(7263,some (fanBlockRows 3511)),(7264,some (fanBlockRows 3512)),(7265,some (fanBlockRows 3513)),(7266,some (fanBlockRows 3514)),(7267,some (fanBlockRows 3515)),(7268,some (fanBlockRows 3516)),(7269,some (fanBlockRows 3517)),(7270,some (fanBlockRows 3518)),(7271,some (fanBlockRows 3519)),(7272,some (fanBlockRows 3521)),(7273,some (fanBlockRows 3522)),(7274,some (fanBlockRows 3523)),(7275,some (fanBlockRows 3524)),(7276,some (fanBlockRows 3525)),(7277,some (fanBlockRows 3526)),(7278,some (fanBlockRows 3527)),(7279,some (fanBlockRows 3528)),(7280,some (fanBlockRows 3529)),(7281,some (fanBlockRows 3530)),(7282,some (fanBlockRows 3532)),(7283,some (fanBlockRows 3533)),(7284,some (fanBlockRows 3534)),(7285,some (fanBlockRows 3535))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step07.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain10_4Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step07.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step07.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain10_4Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain10_4Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step07

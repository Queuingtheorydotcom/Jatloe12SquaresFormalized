import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step09
import Compact.HistoricalCommon.C973.Step09Groups00
import Compact.HistoricalCommon.C973.Step09Groups01
import Compact.HistoricalCommon.C973.Step09Groups02
import Compact.HistoricalCommon.C973.Step09Groups03
import Compact.HistoricalCommon.C973.Step09Groups04
import Compact.HistoricalCommon.C973.Step09Groups05
import Compact.HistoricalCommon.C973.Step09Groups06
import Compact.HistoricalCommon.C973.Step09Groups07

namespace N12Compact.HistoricalCommon.C973.Step09
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
  (.sourceCut 25 (.neighborCut 11 (.sourceCut 6 (.neighborCut 5 .leaf .leaf) (.sourceCut 6 .leaf .leaf)) (.neighborCut 12 .leaf (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 11 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf))) (.sourceCut 6 (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf)) (.neighborCut 11 (.sourceCut 3 .leaf .leaf) .leaf)))))) (.neighborCut 5 (.sourceCut 6 .leaf (.sourceCut 7 .leaf (.neighborCut 2 .leaf .leaf))) (.neighborCut 6 (.sourceCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 7 .leaf .leaf))) (.neighborCut 12 .leaf (.neighborCut 11 .leaf (.sourceCut 13 .leaf (.sourceCut 6 .leaf (.neighborCut 6 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,51,0,46⟩ scopes := by decide +kernel

theorem covered (i : Fin 51) (j : Fin 46) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 51) (j : Fin 46) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8692_header,context8703_header,context8714_header,context8725_header,context8728_header,context8729_header,context8730_header,context8731_header,context8732_header,context8682_header,context8683_header,context8684_header,context8685_header,context8686_header,context8687_header,context8688_header,context8689_header,context8690_header,context8691_header,context8693_header,context8694_header,context8695_header,context8696_header,context8697_header,context8698_header,context8699_header,context8700_header,context8701_header,context8702_header,context8704_header,context8705_header,context8706_header,context8707_header,context8708_header,context8709_header,context8710_header,context8711_header,context8712_header,context8713_header,context8715_header,context8716_header,context8717_header,context8718_header,context8719_header,context8720_header,context8721_header,context8722_header,context8723_header,context8724_header,context8726_header,context8727_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 51).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7701,none),(7702,some (fanBlockRows 3587)),(7703,some (fanBlockRows 3598)),(7704,some (fanBlockRows 3609)),(7705,some (fanBlockRows 3620)),(7706,some (fanBlockRows 3623)),(7707,some (fanBlockRows 3624)),(7708,some (fanBlockRows 3625)),(7709,some (fanBlockRows 3626)),(7710,some (fanBlockRows 3627)),(7711,some (fanBlockRows 3577)),(7712,some (fanBlockRows 3578)),(7713,some (fanBlockRows 3579)),(7714,some (fanBlockRows 3580)),(7715,some (fanBlockRows 3581)),(7716,some (fanBlockRows 3582)),(7717,some (fanBlockRows 3583)),(7718,some (fanBlockRows 3584)),(7719,some (fanBlockRows 3585)),(7720,some (fanBlockRows 3586)),(7721,some (fanBlockRows 3588)),(7722,some (fanBlockRows 3589)),(7723,some (fanBlockRows 3590)),(7724,some (fanBlockRows 3591)),(7725,some (fanBlockRows 3592)),(7726,some (fanBlockRows 3593)),(7727,some (fanBlockRows 3594)),(7728,some (fanBlockRows 3595)),(7729,some (fanBlockRows 3596)),(7730,some (fanBlockRows 3597)),(7731,some (fanBlockRows 3599)),(7732,some (fanBlockRows 3600)),(7733,some (fanBlockRows 3601)),(7734,some (fanBlockRows 3602)),(7735,some (fanBlockRows 3603)),(7736,some (fanBlockRows 3604)),(7737,some (fanBlockRows 3605)),(7738,some (fanBlockRows 3606)),(7739,some (fanBlockRows 3607)),(7740,some (fanBlockRows 3608)),(7741,some (fanBlockRows 3610)),(7742,some (fanBlockRows 3611)),(7743,some (fanBlockRows 3612)),(7744,some (fanBlockRows 3613)),(7745,some (fanBlockRows 3614)),(7746,some (fanBlockRows 3615)),(7747,some (fanBlockRows 3616)),(7748,some (fanBlockRows 3617)),(7749,some (fanBlockRows 3618)),(7750,some (fanBlockRows 3619)),(7751,some (fanBlockRows 3621)),(7752,some (fanBlockRows 3622)),(7753,none),(7754,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step09.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 46).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain9_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step09.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step09.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain9_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain9_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step09

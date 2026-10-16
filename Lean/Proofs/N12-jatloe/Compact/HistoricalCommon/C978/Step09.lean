import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step09
import Compact.HistoricalCommon.C978.Step09Groups00
import Compact.HistoricalCommon.C978.Step09Groups01
import Compact.HistoricalCommon.C978.Step09Groups02
import Compact.HistoricalCommon.C978.Step09Groups03
import Compact.HistoricalCommon.C978.Step09Groups04
import Compact.HistoricalCommon.C978.Step09Groups05
import Compact.HistoricalCommon.C978.Step09Groups06
import Compact.HistoricalCommon.C978.Step09Groups07

namespace N12Compact.HistoricalCommon.C978.Step09
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 30 (.neighborCut 7 (.sourceCut 15 .leaf (.sourceCut 7 .leaf (.neighborCut 3 .leaf .leaf))) (.neighborCut 7 .leaf (.neighborCut 15 .leaf (.sourceCut 15 (.neighborCut 15 .leaf (.sourceCut 7 (.neighborCut 7 .leaf .leaf) .leaf)) (.neighborCut 15 (.sourceCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)))) .leaf))))) (.neighborCut 14 (.sourceCut 15 (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf)) .leaf) (.neighborCut 15 .leaf (.sourceCut 15 (.neighborCut 15 .leaf (.sourceCut 7 .leaf (.neighborCut 7 .leaf .leaf))) (.sourceCut 8 (.neighborCut 15 (.sourceCut 4 .leaf .leaf) (.neighborCut 7 .leaf .leaf)) (.neighborCut 15 .leaf (.neighborCut 7 .leaf .leaf)))))))

theorem partition_checked : partition.Check ⟨0,61,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 61) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 61) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9701_header,context9712_header,context9723_header,context9734_header,context9738_header,context9739_header,context9740_header,context9741_header,context9681_header,context9682_header,context9683_header,context9684_header,context9685_header,context9686_header,context9687_header,context9688_header,context9689_header,context9690_header,context9691_header,context9692_header,context9693_header,context9694_header,context9695_header,context9696_header,context9697_header,context9698_header,context9699_header,context9700_header,context9702_header,context9703_header,context9704_header,context9705_header,context9706_header,context9707_header,context9708_header,context9709_header,context9710_header,context9711_header,context9713_header,context9714_header,context9715_header,context9716_header,context9717_header,context9718_header,context9719_header,context9720_header,context9721_header,context9722_header,context9724_header,context9725_header,context9726_header,context9727_header,context9728_header,context9729_header,context9730_header,context9731_header,context9732_header,context9733_header,context9735_header,context9736_header,context9737_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 61).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8377,none),(8378,none),(8379,some (fanBlockRows 4070)),(8380,some (fanBlockRows 4081)),(8381,some (fanBlockRows 4092)),(8382,some (fanBlockRows 4103)),(8383,some (fanBlockRows 4107)),(8384,some (fanBlockRows 4108)),(8385,some (fanBlockRows 4109)),(8386,some (fanBlockRows 4110)),(8387,some (fanBlockRows 4050)),(8388,some (fanBlockRows 4051)),(8389,some (fanBlockRows 4052)),(8390,some (fanBlockRows 4053)),(8391,some (fanBlockRows 4054)),(8392,some (fanBlockRows 4055)),(8393,some (fanBlockRows 4056)),(8394,some (fanBlockRows 4057)),(8395,some (fanBlockRows 4058)),(8396,some (fanBlockRows 4059)),(8397,some (fanBlockRows 4060)),(8398,some (fanBlockRows 4061)),(8399,some (fanBlockRows 4062)),(8400,some (fanBlockRows 4063)),(8401,some (fanBlockRows 4064)),(8402,some (fanBlockRows 4065)),(8403,some (fanBlockRows 4066)),(8404,some (fanBlockRows 4067)),(8405,some (fanBlockRows 4068)),(8406,some (fanBlockRows 4069)),(8407,some (fanBlockRows 4071)),(8408,some (fanBlockRows 4072)),(8409,some (fanBlockRows 4073)),(8410,some (fanBlockRows 4074)),(8411,some (fanBlockRows 4075)),(8412,some (fanBlockRows 4076)),(8413,some (fanBlockRows 4077)),(8414,some (fanBlockRows 4078)),(8415,some (fanBlockRows 4079)),(8416,some (fanBlockRows 4080)),(8417,some (fanBlockRows 4082)),(8418,some (fanBlockRows 4083)),(8419,some (fanBlockRows 4084)),(8420,some (fanBlockRows 4085)),(8421,some (fanBlockRows 4086)),(8422,some (fanBlockRows 4087)),(8423,some (fanBlockRows 4088)),(8424,some (fanBlockRows 4089)),(8425,some (fanBlockRows 4090)),(8426,some (fanBlockRows 4091)),(8427,some (fanBlockRows 4093)),(8428,some (fanBlockRows 4094)),(8429,some (fanBlockRows 4095)),(8430,some (fanBlockRows 4096)),(8431,some (fanBlockRows 4097)),(8432,some (fanBlockRows 4098)),(8433,some (fanBlockRows 4099)),(8434,some (fanBlockRows 4100)),(8435,some (fanBlockRows 4101)),(8436,some (fanBlockRows 4102)),(8437,some (fanBlockRows 4104)),(8438,some (fanBlockRows 4105)),(8439,some (fanBlockRows 4106)),(8440,none)]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step09.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step09.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step09.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step09

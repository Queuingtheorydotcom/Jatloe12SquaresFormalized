import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step12
import Compact.HistoricalCommon.C978.Step12Groups00
import Compact.HistoricalCommon.C978.Step12Groups01
import Compact.HistoricalCommon.C978.Step12Groups02
import Compact.HistoricalCommon.C978.Step12Groups03
import Compact.HistoricalCommon.C978.Step12Groups04
import Compact.HistoricalCommon.C978.Step12Groups05
import Compact.HistoricalCommon.C978.Step12Groups06
import Compact.HistoricalCommon.C978.Step12Groups07
import Compact.HistoricalCommon.C978.Step12Groups08
import Compact.HistoricalCommon.C978.Step12Groups09
import Compact.HistoricalCommon.C978.Step12Groups10

namespace N12Compact.HistoricalCommon.C978.Step12
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 7 (.sourceCut 8 .leaf (.sourceCut 8 .leaf (.neighborCut 3 .leaf .leaf))) (.neighborCut 8 (.sourceCut 4 .leaf (.sourceCut 4 .leaf (.sourceCut 8 .leaf .leaf))) (.neighborCut 15 .leaf (.sourceCut 8 (.neighborCut 7 .leaf (.neighborCut 8 .leaf .leaf)) (.sourceCut 8 (.neighborCut 15 .leaf (.neighborCut 7 .leaf .leaf)) (.neighborCut 15 .leaf (.neighborCut 7 .leaf (.neighborCut 4 .leaf .leaf)))))))) (.neighborCut 15 (.sourceCut 16 (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf)) (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 15 .leaf (.sourceCut 8 (.neighborCut 15 .leaf (.neighborCut 7 .leaf .leaf)) (.sourceCut 8 (.neighborCut 15 (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)) .leaf) (.sourceCut 8 (.neighborCut 15 .leaf (.neighborCut 7 .leaf (.neighborCut 4 .leaf .leaf))) (.neighborCut 15 (.sourceCut 4 .leaf (.neighborCut 7 .leaf .leaf)) .leaf)))))))

theorem partition_checked : partition.Check ⟨0,64,0,60⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 60) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 60) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9019_header,context9090_header,context9101_header,context9112_header,context9123_header,context9134_header,context9139_header,context9140_header,context9141_header,context9142_header,context9080_header,context9081_header,context9082_header,context9083_header,context9084_header,context9085_header,context9086_header,context9087_header,context9088_header,context9089_header,context9091_header,context9092_header,context9093_header,context9094_header,context9095_header,context9096_header,context9097_header,context9098_header,context9099_header,context9100_header,context9102_header,context9103_header,context9104_header,context9105_header,context9106_header,context9107_header,context9108_header,context9109_header,context9110_header,context9111_header,context9113_header,context9114_header,context9115_header,context9116_header,context9117_header,context9118_header,context9119_header,context9120_header,context9121_header,context9122_header,context9124_header,context9125_header,context9126_header,context9127_header,context9128_header,context9129_header,context9130_header,context9131_header,context9132_header,context9133_header,context9135_header,context9136_header,context9137_header,context9138_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7865,some (fanBlockRows 3816)),(7866,some (fanBlockRows 3827)),(7867,some (fanBlockRows 3838)),(7868,some (fanBlockRows 3849)),(7869,some (fanBlockRows 3856)),(7870,some (fanBlockRows 3867)),(7871,some (fanBlockRows 3872)),(7872,some (fanBlockRows 3873)),(7873,some (fanBlockRows 3874)),(7874,some (fanBlockRows 3875)),(7875,some (fanBlockRows 3817)),(7876,some (fanBlockRows 3818)),(7877,some (fanBlockRows 3819)),(7878,some (fanBlockRows 3820)),(7879,some (fanBlockRows 3821)),(7880,some (fanBlockRows 3822)),(7881,some (fanBlockRows 3823)),(7882,some (fanBlockRows 3824)),(7883,some (fanBlockRows 3825)),(7884,some (fanBlockRows 3826)),(7885,some (fanBlockRows 3828)),(7886,some (fanBlockRows 3829)),(7887,some (fanBlockRows 3830)),(7888,some (fanBlockRows 3831)),(7889,some (fanBlockRows 3832)),(7890,some (fanBlockRows 3833)),(7891,some (fanBlockRows 3834)),(7892,some (fanBlockRows 3835)),(7893,some (fanBlockRows 3836)),(7894,some (fanBlockRows 3837)),(7895,some (fanBlockRows 3839)),(7896,some (fanBlockRows 3840)),(7897,some (fanBlockRows 3841)),(7898,some (fanBlockRows 3842)),(7899,some (fanBlockRows 3843)),(7900,some (fanBlockRows 3844)),(7901,some (fanBlockRows 3845)),(7902,some (fanBlockRows 3846)),(7903,some (fanBlockRows 3847)),(7904,some (fanBlockRows 3848)),(7905,some (fanBlockRows 3850)),(7906,some (fanBlockRows 59)),(7907,some (fanBlockRows 59)),(7908,some (fanBlockRows 59)),(7909,some (fanBlockRows 59)),(7910,some (fanBlockRows 3851)),(7911,some (fanBlockRows 3852)),(7912,some (fanBlockRows 3853)),(7913,some (fanBlockRows 3854)),(7914,some (fanBlockRows 3855)),(7915,some (fanBlockRows 3857)),(7916,some (fanBlockRows 3858)),(7917,some (fanBlockRows 3859)),(7918,some (fanBlockRows 3860)),(7919,some (fanBlockRows 3861)),(7920,some (fanBlockRows 3862)),(7921,some (fanBlockRows 3863)),(7922,some (fanBlockRows 3864)),(7923,some (fanBlockRows 3865)),(7924,some (fanBlockRows 3866)),(7925,some (fanBlockRows 3868)),(7926,some (fanBlockRows 3869)),(7927,some (fanBlockRows 3870)),(7928,some (fanBlockRows 3871))]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step12.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 60).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain6_11Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step12.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step12.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain6_11Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain6_11Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step12

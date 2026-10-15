import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step08
import Compact.HistoricalCommon.C978.Step08Groups00
import Compact.HistoricalCommon.C978.Step08Groups01
import Compact.HistoricalCommon.C978.Step08Groups02
import Compact.HistoricalCommon.C978.Step08Groups03
import Compact.HistoricalCommon.C978.Step08Groups04
import Compact.HistoricalCommon.C978.Step08Groups05
import Compact.HistoricalCommon.C978.Step08Groups06
import Compact.HistoricalCommon.C978.Step08Groups07

namespace N12Compact.HistoricalCommon.C978.Step08
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
  (.neighborCut 15 (.sourceCut 27 .leaf (.sourceCut 7 (.neighborCut 7 .leaf .leaf) (.sourceCut 7 (.neighborCut 7 (.sourceCut 3 .leaf .leaf) .leaf) .leaf))) (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 4 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 (.sourceCut 6 .leaf .leaf) .leaf)))) (.sourceCut 14 (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf .leaf))) (.sourceCut 14 (.neighborCut 8 (.sourceCut 7 .leaf .leaf) (.neighborCut 8 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 7 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 4 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,55,0,63⟩ scopes := by decide +kernel

theorem covered (i : Fin 55) (j : Fin 63) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 55) (j : Fin 63) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9677_header,context9678_header,context9679_header,context9680_header,context9568_header,context9627_header,context9628_header,context9629_header,context9630_header,context9631_header,context9632_header,context9633_header,context9634_header,context9635_header,context9636_header,context9637_header,context9638_header,context9639_header,context9640_header,context9641_header,context9642_header,context9643_header,context9644_header,context9645_header,context9646_header,context9647_header,context9648_header,context9649_header,context9650_header,context9651_header,context9652_header,context9653_header,context9654_header,context9655_header,context9656_header,context9657_header,context9658_header,context9659_header,context9660_header,context9661_header,context9662_header,context9663_header,context9664_header,context9665_header,context9666_header,context9667_header,context9668_header,context9669_header,context9670_header,context9671_header,context9672_header,context9673_header,context9674_header,context9675_header,context9676_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 55).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8189,none),(8190,none),(8191,none),(8192,none),(8193,none),(8194,none),(8195,some (fanBlockRows 4046)),(8196,some (fanBlockRows 4047)),(8197,some (fanBlockRows 4048)),(8198,some (fanBlockRows 4049)),(8199,some (fanBlockRows 3995)),(8200,some (fanBlockRows 3996)),(8201,some (fanBlockRows 3997)),(8202,some (fanBlockRows 3998)),(8203,some (fanBlockRows 3999)),(8204,some (fanBlockRows 4000)),(8205,some (fanBlockRows 4001)),(8206,some (fanBlockRows 4002)),(8207,some (fanBlockRows 4003)),(8208,some (fanBlockRows 4004)),(8209,some (fanBlockRows 4005)),(8210,some (fanBlockRows 4006)),(8211,some (fanBlockRows 4007)),(8212,some (fanBlockRows 4008)),(8213,some (fanBlockRows 4009)),(8214,some (fanBlockRows 4010)),(8215,some (fanBlockRows 4011)),(8216,some (fanBlockRows 4012)),(8217,some (fanBlockRows 4013)),(8218,some (fanBlockRows 4014)),(8219,some (fanBlockRows 4015)),(8220,some (fanBlockRows 4016)),(8221,some (fanBlockRows 4017)),(8222,some (fanBlockRows 4018)),(8223,some (fanBlockRows 4019)),(8224,some (fanBlockRows 4020)),(8225,some (fanBlockRows 4021)),(8226,some (fanBlockRows 4022)),(8227,some (fanBlockRows 4023)),(8228,some (fanBlockRows 4024)),(8229,some (fanBlockRows 4025)),(8230,some (fanBlockRows 4026)),(8231,some (fanBlockRows 4027)),(8232,some (fanBlockRows 4028)),(8233,some (fanBlockRows 4029)),(8234,some (fanBlockRows 4030)),(8235,some (fanBlockRows 4031)),(8236,some (fanBlockRows 4032)),(8237,some (fanBlockRows 4033)),(8238,some (fanBlockRows 4034)),(8239,some (fanBlockRows 4035)),(8240,some (fanBlockRows 4036)),(8241,some (fanBlockRows 4037)),(8242,some (fanBlockRows 4038)),(8243,some (fanBlockRows 4039)),(8244,some (fanBlockRows 4040)),(8245,some (fanBlockRows 4041)),(8246,some (fanBlockRows 4042)),(8247,some (fanBlockRows 4043)),(8248,some (fanBlockRows 4044)),(8249,some (fanBlockRows 4045)),(8250,none),(8251,none),(8252,none)]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step08.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 63).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain5_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step08.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step08.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain5_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain5_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step08

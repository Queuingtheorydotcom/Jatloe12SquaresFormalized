import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step07
import Compact.HistoricalCommon.C978.Step07Groups00
import Compact.HistoricalCommon.C978.Step07Groups01
import Compact.HistoricalCommon.C978.Step07Groups02
import Compact.HistoricalCommon.C978.Step07Groups03
import Compact.HistoricalCommon.C978.Step07Groups04
import Compact.HistoricalCommon.C978.Step07Groups05
import Compact.HistoricalCommon.C978.Step07Groups06
import Compact.HistoricalCommon.C978.Step07Groups07
import Compact.HistoricalCommon.C978.Step07Groups08
import Compact.HistoricalCommon.C978.Step07Groups09
import Compact.HistoricalCommon.C978.Step07Groups10

namespace N12Compact.HistoricalCommon.C978.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.sourceCut 3 .leaf (.neighborCut 1 .leaf .leaf)))) (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))) (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))) (.sourceCut 8 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))) (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))) (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))) (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))) (.neighborCut 6 (.sourceCut 4 .leaf (.neighborCut 3 .leaf (.neighborCut 1 .leaf .leaf))) (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,58,0,12⟩ scopes := by decide +kernel

theorem covered (i : Fin 58) (j : Fin 12) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 58) (j : Fin 12) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9560_header,context9564_header,context9565_header,context9566_header,context9567_header,context9511_header,context9512_header,context9513_header,context9514_header,context9515_header,context9516_header,context9517_header,context9518_header,context9519_header,context9520_header,context9521_header,context9522_header,context9523_header,context9524_header,context9525_header,context9526_header,context9527_header,context9528_header,context9529_header,context6924_header,context9530_header,context9531_header,context9532_header,context9533_header,context9534_header,context9535_header,context9536_header,context9537_header,context9538_header,context9539_header,context9540_header,context9541_header,context9542_header,context9543_header,context9544_header,context9545_header,context9546_header,context9547_header,context9548_header,context9549_header,context9550_header,context9551_header,context9552_header,context9553_header,context9554_header,context9555_header,context9556_header,context9557_header,context9558_header,context9559_header,context9561_header,context9562_header,context9563_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 58).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6683,none),(6684,none),(6685,none),(6686,none),(6687,none),(6688,some (fanBlockRows 3987)),(6689,some (fanBlockRows 3991)),(6690,some (fanBlockRows 3992)),(1197,some (fanBlockRows 3993)),(1198,some (fanBlockRows 3994)),(1199,some (fanBlockRows 3938)),(1200,some (fanBlockRows 3939)),(1201,some (fanBlockRows 3940)),(1202,some (fanBlockRows 3941)),(1203,some (fanBlockRows 3942)),(1204,some (fanBlockRows 3943)),(1205,some (fanBlockRows 3944)),(1206,some (fanBlockRows 3945)),(1207,some (fanBlockRows 3946)),(1208,some (fanBlockRows 3947)),(1209,some (fanBlockRows 3948)),(1210,some (fanBlockRows 3949)),(1211,some (fanBlockRows 3950)),(6691,some (fanBlockRows 3951)),(6692,some (fanBlockRows 3952)),(6693,some (fanBlockRows 3953)),(6694,some (fanBlockRows 3954)),(6695,some (fanBlockRows 3955)),(6696,some (fanBlockRows 3956)),(1218,some (fanBlockRows 59)),(1219,some (fanBlockRows 3957)),(1220,some (fanBlockRows 3958)),(1221,some (fanBlockRows 3959)),(1222,some (fanBlockRows 3960)),(1223,some (fanBlockRows 3961)),(1224,some (fanBlockRows 3962)),(1225,some (fanBlockRows 3963)),(6697,some (fanBlockRows 3964)),(6698,some (fanBlockRows 3965)),(6699,some (fanBlockRows 3966)),(6700,some (fanBlockRows 3967)),(6701,some (fanBlockRows 3968)),(6702,some (fanBlockRows 3969)),(6703,some (fanBlockRows 3970)),(6704,some (fanBlockRows 3971)),(6705,some (fanBlockRows 3972)),(6706,some (fanBlockRows 3973)),(6707,some (fanBlockRows 3974)),(6708,some (fanBlockRows 3975)),(6709,some (fanBlockRows 3976)),(6710,some (fanBlockRows 3977)),(6711,some (fanBlockRows 3978)),(6712,some (fanBlockRows 3979)),(6713,some (fanBlockRows 3980)),(6714,some (fanBlockRows 3981)),(6715,some (fanBlockRows 3982)),(8123,some (fanBlockRows 3983)),(8124,some (fanBlockRows 3984)),(8125,some (fanBlockRows 3985)),(8126,some (fanBlockRows 3986)),(8127,some (fanBlockRows 3988)),(8128,some (fanBlockRows 3989)),(8129,some (fanBlockRows 3990)),(8130,none)]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step07.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 12).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain7_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step07.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step07.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain7_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain7_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step07

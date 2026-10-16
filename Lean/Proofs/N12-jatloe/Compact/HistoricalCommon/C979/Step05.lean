import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step05
import Compact.HistoricalCommon.C979.Step05Groups00
import Compact.HistoricalCommon.C979.Step05Groups01
import Compact.HistoricalCommon.C979.Step05Groups02
import Compact.HistoricalCommon.C979.Step05Groups03
import Compact.HistoricalCommon.C979.Step05Groups04
import Compact.HistoricalCommon.C979.Step05Groups05
import Compact.HistoricalCommon.C979.Step05Groups06
import Compact.HistoricalCommon.C979.Step05Groups07
import Compact.HistoricalCommon.C979.Step05Groups08

namespace N12Compact.HistoricalCommon.C979.Step05
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 30 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 15 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 16 (.sourceCut 15 .leaf (.neighborCut 8 .leaf .leaf)) .leaf))))) (.sourceCut 30 (.neighborCut 32 .leaf (.neighborCut 16 (.sourceCut 15 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf .leaf))))) (.neighborCut 16 (.sourceCut 30 .leaf (.sourceCut 15 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 16 (.sourceCut 15 .leaf (.sourceCut 15 (.neighborCut 8 .leaf .leaf) .leaf)) (.neighborCut 32 .leaf (.sourceCut 30 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 15 .leaf (.sourceCut 7 .leaf .leaf)) .leaf)) (.neighborCut 32 .leaf (.neighborCut 16 (.sourceCut 15 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,120,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 120) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 120) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context12647_header,context12658_header,context12669_header,context12680_header,context12571_header,context12582_header,context12589_header,context12590_header,context12591_header,context12592_header,context12593_header,context12594_header,context12595_header,context12596_header,context12597_header,context12598_header,context12599_header,context12600_header,context12601_header,context12602_header,context12603_header,context12604_header,context12605_header,context12606_header,context12607_header,context12608_header,context12609_header,context12610_header,context12611_header,context12612_header,context12613_header,context12614_header,context12615_header,context12616_header,context12617_header,context12618_header,context12619_header,context12620_header,context12621_header,context12622_header,context12623_header,context12624_header,context12625_header,context12626_header,context12627_header,context12628_header,context12629_header,context12630_header,context12631_header,context12632_header,context12633_header,context12634_header,context12635_header,context12636_header,context12637_header,context12638_header,context12639_header,context12640_header,context12641_header,context12642_header,context12643_header,context12644_header,context12645_header,context12646_header,context12648_header,context12649_header,context12650_header,context12651_header,context12652_header,context12653_header,context12654_header,context12655_header,context12656_header,context12657_header,context12659_header,context12660_header,context12661_header,context12662_header,context12663_header,context12664_header,context12665_header,context12666_header,context12667_header,context12668_header,context12670_header,context12671_header,context12672_header,context12673_header,context12674_header,context12675_header,context12676_header,context12677_header,context12678_header,context12679_header,context12466_header,context12562_header,context12563_header,context12564_header,context12565_header,context12566_header,context12567_header,context12568_header,context12569_header,context12570_header,context12572_header,context12573_header,context12574_header,context12575_header,context12576_header,context12577_header,context12578_header,context12579_header,context12580_header,context12581_header,context12583_header,context12584_header,context12585_header,context12586_header,context12587_header,context12588_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 120).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8929,none),(8930,none),(8931,none),(8932,none),(8933,none),(8934,none),(8935,some (fanBlockRows 5377)),(8936,some (fanBlockRows 5388)),(8937,some (fanBlockRows 5399)),(8938,some (fanBlockRows 5410)),(8939,some (fanBlockRows 5301)),(8940,some (fanBlockRows 5312)),(8941,some (fanBlockRows 5319)),(8942,some (fanBlockRows 5320)),(8943,some (fanBlockRows 5321)),(8944,some (fanBlockRows 5322)),(8945,some (fanBlockRows 5323)),(8946,some (fanBlockRows 5324)),(8947,some (fanBlockRows 5325)),(8948,some (fanBlockRows 5326)),(8949,some (fanBlockRows 5327)),(8950,some (fanBlockRows 5328)),(8951,some (fanBlockRows 5329)),(8952,some (fanBlockRows 5330)),(8953,some (fanBlockRows 5331)),(8954,some (fanBlockRows 5332)),(8955,some (fanBlockRows 5333)),(8956,some (fanBlockRows 5334)),(8957,some (fanBlockRows 5335)),(8958,some (fanBlockRows 5336)),(8959,some (fanBlockRows 5337)),(8960,some (fanBlockRows 5338)),(8961,some (fanBlockRows 5339)),(8962,some (fanBlockRows 5340)),(8963,some (fanBlockRows 5341)),(8964,some (fanBlockRows 5342)),(8965,some (fanBlockRows 5343)),(8966,some (fanBlockRows 5344)),(8967,some (fanBlockRows 5345)),(8968,some (fanBlockRows 5346)),(8969,some (fanBlockRows 5347)),(8970,some (fanBlockRows 5348)),(8971,some (fanBlockRows 5349)),(8972,some (fanBlockRows 5350)),(8973,some (fanBlockRows 5351)),(8974,some (fanBlockRows 5352)),(8975,some (fanBlockRows 5353)),(8976,some (fanBlockRows 5354)),(8977,some (fanBlockRows 5355)),(8978,some (fanBlockRows 5356)),(8979,some (fanBlockRows 5357)),(8980,some (fanBlockRows 5358)),(8981,some (fanBlockRows 5359)),(8982,some (fanBlockRows 5360)),(8983,some (fanBlockRows 5361)),(8984,some (fanBlockRows 5362)),(8985,some (fanBlockRows 5363)),(8986,some (fanBlockRows 5364)),(8987,some (fanBlockRows 5365)),(8988,some (fanBlockRows 5366)),(8989,some (fanBlockRows 5367)),(8990,some (fanBlockRows 5368)),(8991,some (fanBlockRows 5369)),(8992,some (fanBlockRows 5370)),(8993,some (fanBlockRows 5371)),(8994,some (fanBlockRows 5372)),(8995,some (fanBlockRows 5373)),(8996,some (fanBlockRows 5374)),(8997,some (fanBlockRows 5375)),(8998,some (fanBlockRows 5376)),(8999,some (fanBlockRows 5378)),(9000,some (fanBlockRows 5379)),(9001,some (fanBlockRows 5380)),(9002,some (fanBlockRows 5381)),(9003,some (fanBlockRows 5382)),(9004,some (fanBlockRows 5383)),(9005,some (fanBlockRows 5384)),(9006,some (fanBlockRows 5385)),(9007,some (fanBlockRows 5386)),(9008,some (fanBlockRows 5387)),(9009,some (fanBlockRows 5389)),(9010,some (fanBlockRows 5390)),(9011,some (fanBlockRows 5391)),(9012,some (fanBlockRows 5392)),(9013,some (fanBlockRows 5393)),(9014,some (fanBlockRows 5394)),(9015,some (fanBlockRows 5395)),(9016,some (fanBlockRows 5396)),(9017,some (fanBlockRows 5397)),(9018,some (fanBlockRows 5398)),(9019,some (fanBlockRows 5400)),(9020,some (fanBlockRows 5401)),(9021,some (fanBlockRows 5402)),(9022,some (fanBlockRows 5403)),(9023,some (fanBlockRows 5404)),(9024,some (fanBlockRows 5405)),(9025,some (fanBlockRows 5406)),(9026,some (fanBlockRows 5407)),(9027,some (fanBlockRows 5408)),(9028,some (fanBlockRows 5409)),(9029,some (fanBlockRows 5291)),(9030,some (fanBlockRows 5292)),(9031,some (fanBlockRows 5293)),(9032,some (fanBlockRows 5294)),(9033,some (fanBlockRows 5295)),(9034,some (fanBlockRows 5296)),(9035,some (fanBlockRows 5297)),(9036,some (fanBlockRows 5298)),(9037,some (fanBlockRows 5299)),(9038,some (fanBlockRows 5300)),(9039,some (fanBlockRows 5302)),(9040,some (fanBlockRows 5303)),(9041,some (fanBlockRows 5304)),(9042,some (fanBlockRows 5305)),(9043,some (fanBlockRows 5306)),(9044,some (fanBlockRows 5307)),(9045,some (fanBlockRows 5308)),(9046,some (fanBlockRows 5309)),(9047,some (fanBlockRows 5310)),(9048,some (fanBlockRows 5311)),(9049,some (fanBlockRows 5313)),(9050,some (fanBlockRows 5314)),(9051,some (fanBlockRows 5315)),(9052,some (fanBlockRows 5316)),(9053,some (fanBlockRows 5317)),(9054,some (fanBlockRows 5318)),(9055,none),(9056,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step05.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain3_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step05.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step05.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain3_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain3_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step05

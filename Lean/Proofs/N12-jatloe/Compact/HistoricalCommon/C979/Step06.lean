import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step06
import Compact.HistoricalCommon.C979.Step06Groups00
import Compact.HistoricalCommon.C979.Step06Groups01
import Compact.HistoricalCommon.C979.Step06Groups02
import Compact.HistoricalCommon.C979.Step06Groups03
import Compact.HistoricalCommon.C979.Step06Groups04

namespace N12Compact.HistoricalCommon.C979.Step06
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 16 (.sourceCut 30 .leaf (.sourceCut 30 .leaf (.sourceCut 15 .leaf (.sourceCut 15 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))))) (.neighborCut 16 (.sourceCut 15 .leaf (.sourceCut 15 (.neighborCut 8 .leaf .leaf) (.sourceCut 30 (.neighborCut 8 .leaf .leaf) .leaf))) (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.sourceCut 60 .leaf (.sourceCut 30 .leaf (.neighborCut 16 (.sourceCut 15 .leaf .leaf) .leaf)))))))

theorem partition_checked : partition.Check ⟨0,121,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 121) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 121) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context12841_header,context12852_header,context12863_header,context12874_header,context12885_header,context12896_header,context12907_header,context12918_header,context12929_header,context12819_header,context12830_header,context12833_header,context12834_header,context12835_header,context12836_header,context12837_header,context12838_header,context12839_header,context12840_header,context12842_header,context12843_header,context12844_header,context12845_header,context12846_header,context12847_header,context12848_header,context12849_header,context12850_header,context12851_header,context12853_header,context12854_header,context12855_header,context12856_header,context12857_header,context12858_header,context12859_header,context12860_header,context12861_header,context12862_header,context12864_header,context12865_header,context12866_header,context12867_header,context12868_header,context12869_header,context12870_header,context12871_header,context12872_header,context12873_header,context12875_header,context12876_header,context12877_header,context12878_header,context12879_header,context12880_header,context12881_header,context12882_header,context12883_header,context12884_header,context12886_header,context12887_header,context12888_header,context12889_header,context12890_header,context12891_header,context12892_header,context12893_header,context12894_header,context12895_header,context12897_header,context12898_header,context12899_header,context12900_header,context12901_header,context12902_header,context12903_header,context12904_header,context12905_header,context12906_header,context12908_header,context12909_header,context12910_header,context12911_header,context12912_header,context12913_header,context12914_header,context12915_header,context12916_header,context12917_header,context12919_header,context12920_header,context12921_header,context12922_header,context12923_header,context12924_header,context12925_header,context12926_header,context12927_header,context12928_header,context12681_header,context12810_header,context12811_header,context12812_header,context12813_header,context12814_header,context12815_header,context12816_header,context12817_header,context12818_header,context12820_header,context12821_header,context12822_header,context12823_header,context12824_header,context12825_header,context12826_header,context12827_header,context12828_header,context12829_header,context12831_header,context12832_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 121).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(9212,none),(9213,some (fanBlockRows 5443)),(9214,some (fanBlockRows 5454)),(9215,some (fanBlockRows 5465)),(9216,some (fanBlockRows 5476)),(9217,some (fanBlockRows 5487)),(9218,some (fanBlockRows 5498)),(9219,some (fanBlockRows 5509)),(9220,some (fanBlockRows 5520)),(9221,some (fanBlockRows 5531)),(9222,some (fanBlockRows 5421)),(9223,some (fanBlockRows 5432)),(9224,some (fanBlockRows 5435)),(9225,some (fanBlockRows 5436)),(9226,some (fanBlockRows 5437)),(9227,some (fanBlockRows 5438)),(9228,some (fanBlockRows 5439)),(9229,some (fanBlockRows 5440)),(9230,some (fanBlockRows 5441)),(9231,some (fanBlockRows 5442)),(9232,some (fanBlockRows 5444)),(9233,some (fanBlockRows 5445)),(9234,some (fanBlockRows 5446)),(9235,some (fanBlockRows 5447)),(9236,some (fanBlockRows 5448)),(9237,some (fanBlockRows 5449)),(9238,some (fanBlockRows 5450)),(9239,some (fanBlockRows 5451)),(9240,some (fanBlockRows 5452)),(9241,some (fanBlockRows 5453)),(9242,some (fanBlockRows 5455)),(9243,some (fanBlockRows 5456)),(9244,some (fanBlockRows 5457)),(9245,some (fanBlockRows 5458)),(9246,some (fanBlockRows 5459)),(9247,some (fanBlockRows 5460)),(9248,some (fanBlockRows 5461)),(9249,some (fanBlockRows 5462)),(9250,some (fanBlockRows 5463)),(9251,some (fanBlockRows 5464)),(9252,some (fanBlockRows 5466)),(9253,some (fanBlockRows 5467)),(9254,some (fanBlockRows 5468)),(9255,some (fanBlockRows 5469)),(9256,some (fanBlockRows 5470)),(9257,some (fanBlockRows 5471)),(9258,some (fanBlockRows 5472)),(9259,some (fanBlockRows 5473)),(9260,some (fanBlockRows 5474)),(9261,some (fanBlockRows 5475)),(9262,some (fanBlockRows 5477)),(9263,some (fanBlockRows 5478)),(9264,some (fanBlockRows 5479)),(9265,some (fanBlockRows 5480)),(9266,some (fanBlockRows 5481)),(9267,some (fanBlockRows 5482)),(9268,some (fanBlockRows 5483)),(9269,some (fanBlockRows 5484)),(9270,some (fanBlockRows 5485)),(9271,some (fanBlockRows 5486)),(9272,some (fanBlockRows 5488)),(9273,some (fanBlockRows 5489)),(9274,some (fanBlockRows 5490)),(9275,some (fanBlockRows 5491)),(9276,some (fanBlockRows 5492)),(9277,some (fanBlockRows 5493)),(9278,some (fanBlockRows 5494)),(9279,some (fanBlockRows 5495)),(9280,some (fanBlockRows 5496)),(9281,some (fanBlockRows 5497)),(9282,some (fanBlockRows 5499)),(9283,some (fanBlockRows 5500)),(9284,some (fanBlockRows 5501)),(9285,some (fanBlockRows 5502)),(9286,some (fanBlockRows 5503)),(9287,some (fanBlockRows 5504)),(9288,some (fanBlockRows 5505)),(9289,some (fanBlockRows 5506)),(9290,some (fanBlockRows 5507)),(9291,some (fanBlockRows 5508)),(9292,some (fanBlockRows 5510)),(9293,some (fanBlockRows 5511)),(9294,some (fanBlockRows 5512)),(9295,some (fanBlockRows 5513)),(9296,some (fanBlockRows 5514)),(9297,some (fanBlockRows 5515)),(9298,some (fanBlockRows 5516)),(9299,some (fanBlockRows 5517)),(9300,some (fanBlockRows 5518)),(9301,some (fanBlockRows 5519)),(9302,some (fanBlockRows 5521)),(9303,some (fanBlockRows 5522)),(9304,some (fanBlockRows 5523)),(9305,some (fanBlockRows 5524)),(9306,some (fanBlockRows 5525)),(9307,some (fanBlockRows 5526)),(9308,some (fanBlockRows 5527)),(9309,some (fanBlockRows 5528)),(9310,some (fanBlockRows 5529)),(9311,some (fanBlockRows 5530)),(9312,some (fanBlockRows 5411)),(9313,some (fanBlockRows 5412)),(9314,some (fanBlockRows 5413)),(9315,some (fanBlockRows 5414)),(9316,some (fanBlockRows 5415)),(9317,some (fanBlockRows 5416)),(9318,some (fanBlockRows 5417)),(9319,some (fanBlockRows 5418)),(9320,some (fanBlockRows 5419)),(9321,some (fanBlockRows 5420)),(9322,some (fanBlockRows 5422)),(9323,some (fanBlockRows 5423)),(9324,some (fanBlockRows 5424)),(9325,some (fanBlockRows 5425)),(9326,some (fanBlockRows 5426)),(9327,some (fanBlockRows 5427)),(9328,some (fanBlockRows 5428)),(9329,some (fanBlockRows 5429)),(9330,some (fanBlockRows 5430)),(9331,some (fanBlockRows 5431)),(9332,some (fanBlockRows 5433)),(9333,some (fanBlockRows 5434)),(9334,none),(9335,none),(9336,none),(9337,none),(9338,none),(9339,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step06.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain4_4Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step06.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step06.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain4_4Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain4_4Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step06

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step01
import Compact.HistoricalCommon.C979.Step01Groups00
import Compact.HistoricalCommon.C979.Step01Groups01
import Compact.HistoricalCommon.C979.Step01Groups02
import Compact.HistoricalCommon.C979.Step01Groups03
import Compact.HistoricalCommon.C979.Step01Groups04
import Compact.HistoricalCommon.C979.Step01Groups05
import Compact.HistoricalCommon.C979.Step01Groups06
import Compact.HistoricalCommon.C979.Step01Groups07
import Compact.HistoricalCommon.C979.Step01Groups08
import Compact.HistoricalCommon.C979.Step01Groups09
import Compact.HistoricalCommon.C979.Step01Groups10
import Compact.HistoricalCommon.C979.Step01Groups11

namespace N12Compact.HistoricalCommon.C979.Step01
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 28 (.sourceCut 16 (.neighborCut 14 .leaf (.neighborCut 7 .leaf .leaf)) .leaf) (.neighborCut 14 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 15 .leaf (.neighborCut 28 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.neighborCut 14 .leaf .leaf))))))) (.sourceCut 32 (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 16 .leaf (.neighborCut 7 .leaf .leaf)) (.neighborCut 15 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 28 .leaf (.neighborCut 14 .leaf (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf))))))) (.sourceCut 32 (.neighborCut 57 (.sourceCut 16 (.neighborCut 28 .leaf (.neighborCut 14 .leaf (.sourceCut 8 .leaf .leaf))) .leaf) (.neighborCut 28 .leaf (.sourceCut 16 (.neighborCut 14 .leaf .leaf) .leaf))) (.neighborCut 28 (.sourceCut 8 .leaf (.sourceCut 4 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 14 .leaf (.neighborCut 15 .leaf (.neighborCut 28 .leaf (.neighborCut 14 .leaf (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,128,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11267_header,context11306_header,context11317_header,context11328_header,context11339_header,context11350_header,context11361_header,context11372_header,context11383_header,context11394_header,context11278_header,context11289_header,context11298_header,context11299_header,context11300_header,context11301_header,context11302_header,context11303_header,context11304_header,context11305_header,context11307_header,context11308_header,context11309_header,context11310_header,context11311_header,context11312_header,context11313_header,context11314_header,context11315_header,context11316_header,context11318_header,context11319_header,context11320_header,context11321_header,context11322_header,context11323_header,context11324_header,context11325_header,context11326_header,context11327_header,context11329_header,context11330_header,context11331_header,context11332_header,context11333_header,context11334_header,context11335_header,context11336_header,context11337_header,context11338_header,context11340_header,context11341_header,context11342_header,context11343_header,context11344_header,context11345_header,context11346_header,context11347_header,context11348_header,context11349_header,context11351_header,context11352_header,context11353_header,context11354_header,context11355_header,context11356_header,context11357_header,context11358_header,context11359_header,context11360_header,context11362_header,context11363_header,context11364_header,context11365_header,context11366_header,context11367_header,context11368_header,context11369_header,context11370_header,context11371_header,context11373_header,context11374_header,context11375_header,context11376_header,context11377_header,context11378_header,context11379_header,context11380_header,context11381_header,context11382_header,context11384_header,context11385_header,context11386_header,context11387_header,context11388_header,context11389_header,context11390_header,context11391_header,context11392_header,context11393_header,context11268_header,context11269_header,context11270_header,context11271_header,context11272_header,context11273_header,context11274_header,context11275_header,context11276_header,context11277_header,context11279_header,context11280_header,context11281_header,context11282_header,context11283_header,context11284_header,context11285_header,context11286_header,context11287_header,context11288_header,context11290_header,context11291_header,context11292_header,context11293_header,context11294_header,context11295_header,context11296_header,context11297_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(9477,some (fanBlockRows 4747)),(9478,some (fanBlockRows 4786)),(9479,some (fanBlockRows 4797)),(9480,some (fanBlockRows 4808)),(9481,some (fanBlockRows 4819)),(9482,some (fanBlockRows 4830)),(9483,some (fanBlockRows 4841)),(9484,some (fanBlockRows 4852)),(9485,some (fanBlockRows 4863)),(9486,some (fanBlockRows 4874)),(9487,some (fanBlockRows 4758)),(9488,some (fanBlockRows 4769)),(9489,some (fanBlockRows 4778)),(9490,some (fanBlockRows 4779)),(9491,some (fanBlockRows 4780)),(9492,some (fanBlockRows 4781)),(9493,some (fanBlockRows 4782)),(9494,some (fanBlockRows 4783)),(9495,some (fanBlockRows 4784)),(9496,some (fanBlockRows 4785)),(9497,some (fanBlockRows 4787)),(9498,some (fanBlockRows 4788)),(9499,some (fanBlockRows 4789)),(9500,some (fanBlockRows 4790)),(9501,some (fanBlockRows 4791)),(9502,some (fanBlockRows 4792)),(9503,some (fanBlockRows 4793)),(9504,some (fanBlockRows 4794)),(9505,some (fanBlockRows 4795)),(9506,some (fanBlockRows 4796)),(9507,some (fanBlockRows 4798)),(9508,some (fanBlockRows 4799)),(9509,some (fanBlockRows 4800)),(9510,some (fanBlockRows 4801)),(9511,some (fanBlockRows 4802)),(9512,some (fanBlockRows 4803)),(9513,some (fanBlockRows 4804)),(9514,some (fanBlockRows 4805)),(9515,some (fanBlockRows 4806)),(9516,some (fanBlockRows 4807)),(9517,some (fanBlockRows 4809)),(9518,some (fanBlockRows 4810)),(9519,some (fanBlockRows 4811)),(9520,some (fanBlockRows 4812)),(9521,some (fanBlockRows 4813)),(9522,some (fanBlockRows 4814)),(9523,some (fanBlockRows 4815)),(9524,some (fanBlockRows 4816)),(9525,some (fanBlockRows 4817)),(9526,some (fanBlockRows 4818)),(9527,some (fanBlockRows 4820)),(9528,some (fanBlockRows 4821)),(9529,some (fanBlockRows 4822)),(9530,some (fanBlockRows 4823)),(9531,some (fanBlockRows 4824)),(9532,some (fanBlockRows 4825)),(9533,some (fanBlockRows 4826)),(9534,some (fanBlockRows 4827)),(9535,some (fanBlockRows 4828)),(9536,some (fanBlockRows 4829)),(9537,some (fanBlockRows 4831)),(9538,some (fanBlockRows 4832)),(9539,some (fanBlockRows 4833)),(9540,some (fanBlockRows 4834)),(9541,some (fanBlockRows 4835)),(9542,some (fanBlockRows 4836)),(9543,some (fanBlockRows 4837)),(9544,some (fanBlockRows 4838)),(9545,some (fanBlockRows 4839)),(9546,some (fanBlockRows 4840)),(9547,some (fanBlockRows 4842)),(9548,some (fanBlockRows 4843)),(9549,some (fanBlockRows 4844)),(9550,some (fanBlockRows 4845)),(9551,some (fanBlockRows 4846)),(9552,some (fanBlockRows 4847)),(9553,some (fanBlockRows 4848)),(9554,some (fanBlockRows 4849)),(9555,some (fanBlockRows 4850)),(9556,some (fanBlockRows 4851)),(9557,some (fanBlockRows 4853)),(9558,some (fanBlockRows 4854)),(9559,some (fanBlockRows 4855)),(9560,some (fanBlockRows 4856)),(9561,some (fanBlockRows 4857)),(9562,some (fanBlockRows 4858)),(9563,some (fanBlockRows 4859)),(9564,some (fanBlockRows 4860)),(9565,some (fanBlockRows 4861)),(9566,some (fanBlockRows 4862)),(9567,some (fanBlockRows 4864)),(9568,some (fanBlockRows 4865)),(9569,some (fanBlockRows 4866)),(9570,some (fanBlockRows 4867)),(9571,some (fanBlockRows 4868)),(9572,some (fanBlockRows 4869)),(9573,some (fanBlockRows 4870)),(9574,some (fanBlockRows 4871)),(9575,some (fanBlockRows 4872)),(9576,some (fanBlockRows 4873)),(9577,some (fanBlockRows 4748)),(9578,some (fanBlockRows 4749)),(9579,some (fanBlockRows 4750)),(9580,some (fanBlockRows 4751)),(9581,some (fanBlockRows 4752)),(9582,some (fanBlockRows 4753)),(9583,some (fanBlockRows 4754)),(9584,some (fanBlockRows 4755)),(9585,some (fanBlockRows 4756)),(9586,some (fanBlockRows 4757)),(9587,some (fanBlockRows 4759)),(9588,some (fanBlockRows 4760)),(9589,some (fanBlockRows 4761)),(9590,some (fanBlockRows 4762)),(9591,some (fanBlockRows 4763)),(9592,some (fanBlockRows 4764)),(9593,some (fanBlockRows 4765)),(9594,some (fanBlockRows 4766)),(9595,some (fanBlockRows 4767)),(9596,some (fanBlockRows 4768)),(9597,some (fanBlockRows 4770)),(9598,some (fanBlockRows 4771)),(9599,some (fanBlockRows 4772)),(9600,some (fanBlockRows 4773)),(9601,some (fanBlockRows 4774)),(9602,some (fanBlockRows 4775)),(9603,some (fanBlockRows 4776)),(9604,some (fanBlockRows 4777))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step01.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step01.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step01.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step01

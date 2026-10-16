import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step02
import Compact.HistoricalCommon.C979.Step02Groups00
import Compact.HistoricalCommon.C979.Step02Groups01
import Compact.HistoricalCommon.C979.Step02Groups02
import Compact.HistoricalCommon.C979.Step02Groups03
import Compact.HistoricalCommon.C979.Step02Groups04
import Compact.HistoricalCommon.C979.Step02Groups05
import Compact.HistoricalCommon.C979.Step02Groups06
import Compact.HistoricalCommon.C979.Step02Groups07
import Compact.HistoricalCommon.C979.Step02Groups08
import Compact.HistoricalCommon.C979.Step02Groups09

namespace N12Compact.HistoricalCommon.C979.Step02
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 64 (.neighborCut 8 (.sourceCut 32 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 2 .leaf .leaf))))))))) (.sourceCut 32 (.neighborCut 16 (.sourceCut 16 .leaf .leaf) (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 32 (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf))))))) (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 32 (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,128,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11981_header,context12020_header,context12031_header,context12042_header,context12053_header,context12064_header,context12075_header,context12086_header,context12097_header,context12108_header,context11992_header,context12003_header,context12012_header,context12013_header,context12014_header,context12015_header,context12016_header,context12017_header,context12018_header,context12019_header,context12021_header,context12022_header,context12023_header,context12024_header,context12025_header,context12026_header,context12027_header,context12028_header,context12029_header,context12030_header,context12032_header,context12033_header,context12034_header,context12035_header,context12036_header,context12037_header,context12038_header,context12039_header,context12040_header,context12041_header,context12043_header,context12044_header,context12045_header,context12046_header,context12047_header,context12048_header,context12049_header,context12050_header,context12051_header,context12052_header,context12054_header,context12055_header,context12056_header,context12057_header,context12058_header,context12059_header,context12060_header,context12061_header,context12062_header,context12063_header,context12065_header,context12066_header,context12067_header,context12068_header,context12069_header,context12070_header,context12071_header,context12072_header,context12073_header,context12074_header,context12076_header,context12077_header,context12078_header,context12079_header,context12080_header,context12081_header,context12082_header,context12083_header,context12084_header,context12085_header,context12087_header,context12088_header,context12089_header,context12090_header,context12091_header,context12092_header,context12093_header,context12094_header,context12095_header,context12096_header,context12098_header,context12099_header,context12100_header,context12101_header,context12102_header,context12103_header,context12104_header,context12105_header,context12106_header,context12107_header,context11982_header,context11983_header,context11984_header,context11985_header,context11986_header,context11987_header,context11988_header,context11989_header,context11990_header,context11991_header,context11993_header,context11994_header,context11995_header,context11996_header,context11997_header,context11998_header,context11999_header,context12000_header,context12001_header,context12002_header,context12004_header,context12005_header,context12006_header,context12007_header,context12008_header,context12009_header,context12010_header,context12011_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(9733,some (fanBlockRows 4955)),(9734,some (fanBlockRows 4994)),(9735,some (fanBlockRows 5005)),(9736,some (fanBlockRows 5016)),(9737,some (fanBlockRows 5027)),(9738,some (fanBlockRows 5038)),(9739,some (fanBlockRows 5049)),(9740,some (fanBlockRows 5060)),(9741,some (fanBlockRows 5071)),(9742,some (fanBlockRows 5082)),(9743,some (fanBlockRows 4966)),(9744,some (fanBlockRows 4977)),(9745,some (fanBlockRows 4986)),(9746,some (fanBlockRows 4987)),(9747,some (fanBlockRows 4988)),(9748,some (fanBlockRows 4989)),(9749,some (fanBlockRows 4990)),(9750,some (fanBlockRows 4991)),(9751,some (fanBlockRows 4992)),(9752,some (fanBlockRows 4993)),(9753,some (fanBlockRows 4995)),(9754,some (fanBlockRows 4996)),(9755,some (fanBlockRows 4997)),(9756,some (fanBlockRows 4998)),(9757,some (fanBlockRows 4999)),(9758,some (fanBlockRows 5000)),(9759,some (fanBlockRows 5001)),(9760,some (fanBlockRows 5002)),(9761,some (fanBlockRows 5003)),(9762,some (fanBlockRows 5004)),(9763,some (fanBlockRows 5006)),(9764,some (fanBlockRows 5007)),(9765,some (fanBlockRows 5008)),(9766,some (fanBlockRows 5009)),(9767,some (fanBlockRows 5010)),(9768,some (fanBlockRows 5011)),(9769,some (fanBlockRows 5012)),(9770,some (fanBlockRows 5013)),(9771,some (fanBlockRows 5014)),(9772,some (fanBlockRows 5015)),(9773,some (fanBlockRows 5017)),(9774,some (fanBlockRows 5018)),(9775,some (fanBlockRows 5019)),(9776,some (fanBlockRows 5020)),(9777,some (fanBlockRows 5021)),(9778,some (fanBlockRows 5022)),(9779,some (fanBlockRows 5023)),(9780,some (fanBlockRows 5024)),(9781,some (fanBlockRows 5025)),(9782,some (fanBlockRows 5026)),(9783,some (fanBlockRows 5028)),(9784,some (fanBlockRows 5029)),(9785,some (fanBlockRows 5030)),(9786,some (fanBlockRows 5031)),(9787,some (fanBlockRows 5032)),(9788,some (fanBlockRows 5033)),(9789,some (fanBlockRows 5034)),(9790,some (fanBlockRows 5035)),(9791,some (fanBlockRows 5036)),(9792,some (fanBlockRows 5037)),(9793,some (fanBlockRows 5039)),(9794,some (fanBlockRows 5040)),(9795,some (fanBlockRows 5041)),(9796,some (fanBlockRows 5042)),(9797,some (fanBlockRows 5043)),(9798,some (fanBlockRows 5044)),(9799,some (fanBlockRows 5045)),(9800,some (fanBlockRows 5046)),(9801,some (fanBlockRows 5047)),(9802,some (fanBlockRows 5048)),(9803,some (fanBlockRows 5050)),(9804,some (fanBlockRows 5051)),(9805,some (fanBlockRows 5052)),(9806,some (fanBlockRows 5053)),(9807,some (fanBlockRows 5054)),(9808,some (fanBlockRows 5055)),(9809,some (fanBlockRows 5056)),(9810,some (fanBlockRows 5057)),(9811,some (fanBlockRows 5058)),(9812,some (fanBlockRows 5059)),(9813,some (fanBlockRows 5061)),(9814,some (fanBlockRows 5062)),(9815,some (fanBlockRows 5063)),(9816,some (fanBlockRows 5064)),(9817,some (fanBlockRows 5065)),(9818,some (fanBlockRows 5066)),(9819,some (fanBlockRows 5067)),(9820,some (fanBlockRows 5068)),(9821,some (fanBlockRows 5069)),(9822,some (fanBlockRows 5070)),(9823,some (fanBlockRows 5072)),(9824,some (fanBlockRows 5073)),(9825,some (fanBlockRows 5074)),(9826,some (fanBlockRows 5075)),(9827,some (fanBlockRows 5076)),(9828,some (fanBlockRows 5077)),(9829,some (fanBlockRows 5078)),(9830,some (fanBlockRows 5079)),(9831,some (fanBlockRows 5080)),(9832,some (fanBlockRows 5081)),(9833,some (fanBlockRows 4956)),(9834,some (fanBlockRows 4957)),(9835,some (fanBlockRows 4958)),(9836,some (fanBlockRows 4959)),(9837,some (fanBlockRows 4960)),(9838,some (fanBlockRows 4961)),(9839,some (fanBlockRows 4962)),(9840,some (fanBlockRows 4963)),(9841,some (fanBlockRows 4964)),(9842,some (fanBlockRows 4965)),(9843,some (fanBlockRows 4967)),(9844,some (fanBlockRows 4968)),(9845,some (fanBlockRows 4969)),(9846,some (fanBlockRows 4970)),(9847,some (fanBlockRows 4971)),(9848,some (fanBlockRows 4972)),(9849,some (fanBlockRows 4973)),(9850,some (fanBlockRows 4974)),(9851,some (fanBlockRows 4975)),(9852,some (fanBlockRows 4976)),(9853,some (fanBlockRows 4978)),(9854,some (fanBlockRows 4979)),(9855,some (fanBlockRows 4980)),(9856,some (fanBlockRows 4981)),(9857,some (fanBlockRows 4982)),(9858,some (fanBlockRows 4983)),(9859,some (fanBlockRows 4984)),(9860,some (fanBlockRows 4985))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step02.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step02.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step02.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step02

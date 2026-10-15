import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step04
import Compact.HistoricalCommon.C717.Step04Groups00
import Compact.HistoricalCommon.C717.Step04Groups01
import Compact.HistoricalCommon.C717.Step04Groups02
import Compact.HistoricalCommon.C717.Step04Groups03
import Compact.HistoricalCommon.C717.Step04Groups04
import Compact.HistoricalCommon.C717.Step04Groups05
import Compact.HistoricalCommon.C717.Step04Groups06

namespace N12Compact.HistoricalCommon.C717.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 28 (.sourceCut 27 (.neighborCut 14 .leaf (.neighborCut 7 .leaf .leaf)) (.sourceCut 27 (.neighborCut 14 .leaf (.sourceCut 13 .leaf .leaf)) (.sourceCut 27 (.neighborCut 14 .leaf .leaf) .leaf))) (.neighborCut 28 .leaf (.sourceCut 27 (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.neighborCut 7 (.sourceCut 13 .leaf .leaf) (.neighborCut 14 (.sourceCut 13 .leaf .leaf) .leaf)))) (.sourceCut 27 (.neighborCut 28 .leaf .leaf) (.sourceCut 27 (.neighborCut 28 .leaf .leaf) (.neighborCut 28 (.sourceCut 14 (.neighborCut 14 .leaf .leaf) .leaf) (.neighborCut 14 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,109,0,113⟩ scopes := by decide +kernel

theorem covered (i : Fin 109) (j : Fin 113) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 109) (j : Fin 113) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context5593_header,context5604_header,context5506_header,context5514_header,context5515_header,context5516_header,context5517_header,context5518_header,context5519_header,context5520_header,context5521_header,context5522_header,context5523_header,context5524_header,context5525_header,context5526_header,context5527_header,context5528_header,context5529_header,context5530_header,context5531_header,context5532_header,context5533_header,context5534_header,context5535_header,context5536_header,context5537_header,context5538_header,context5539_header,context5540_header,context5541_header,context5542_header,context5543_header,context5544_header,context5545_header,context5546_header,context5547_header,context5548_header,context5549_header,context5550_header,context5551_header,context5552_header,context5553_header,context5554_header,context5555_header,context5556_header,context5557_header,context5558_header,context5559_header,context5560_header,context5561_header,context5562_header,context5563_header,context5564_header,context5565_header,context5566_header,context5567_header,context5568_header,context5569_header,context5570_header,context5571_header,context5572_header,context5573_header,context5574_header,context5575_header,context5576_header,context5577_header,context5578_header,context5579_header,context5580_header,context5581_header,context5582_header,context5583_header,context5584_header,context5585_header,context5586_header,context5587_header,context5588_header,context5589_header,context5590_header,context5591_header,context5592_header,context5594_header,context5595_header,context5596_header,context5597_header,context5598_header,context5599_header,context5600_header,context5601_header,context5602_header,context5603_header,context5496_header,context5497_header,context5498_header,context5499_header,context5500_header,context5501_header,context5502_header,context5503_header,context5504_header,context5505_header,context5507_header,context5508_header,context5509_header,context5510_header,context5511_header,context5512_header,context5513_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 109).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(4875,none),(4876,none),(4877,none),(4878,none),(4879,none),(4880,none),(4881,none),(4882,none),(4883,some (fanBlockRows 2213)),(4884,some (fanBlockRows 2224)),(4885,some (fanBlockRows 2126)),(4886,some (fanBlockRows 2134)),(4887,some (fanBlockRows 2135)),(4888,some (fanBlockRows 2136)),(4889,some (fanBlockRows 2137)),(4890,some (fanBlockRows 2138)),(4891,some (fanBlockRows 2139)),(4892,some (fanBlockRows 2140)),(4893,some (fanBlockRows 2141)),(4894,some (fanBlockRows 2142)),(4895,some (fanBlockRows 2143)),(4896,some (fanBlockRows 2144)),(4897,some (fanBlockRows 2145)),(4898,some (fanBlockRows 2146)),(4899,some (fanBlockRows 2147)),(4900,some (fanBlockRows 2148)),(4901,some (fanBlockRows 2149)),(4902,some (fanBlockRows 2150)),(4903,some (fanBlockRows 2151)),(4904,some (fanBlockRows 2152)),(4905,some (fanBlockRows 2153)),(4906,some (fanBlockRows 2154)),(4907,some (fanBlockRows 2155)),(4908,some (fanBlockRows 2156)),(4909,some (fanBlockRows 2157)),(4910,some (fanBlockRows 2158)),(4911,some (fanBlockRows 2159)),(4912,some (fanBlockRows 2160)),(4913,some (fanBlockRows 2161)),(4914,some (fanBlockRows 2162)),(4915,some (fanBlockRows 2163)),(4916,some (fanBlockRows 2164)),(4917,some (fanBlockRows 2165)),(4918,some (fanBlockRows 2166)),(4919,some (fanBlockRows 2167)),(4920,some (fanBlockRows 2168)),(4921,some (fanBlockRows 2169)),(4922,some (fanBlockRows 2170)),(4923,some (fanBlockRows 2171)),(4924,some (fanBlockRows 2172)),(4925,some (fanBlockRows 2173)),(4926,some (fanBlockRows 2174)),(4927,some (fanBlockRows 2175)),(4928,some (fanBlockRows 2176)),(4929,some (fanBlockRows 2177)),(4930,some (fanBlockRows 2178)),(4931,some (fanBlockRows 2179)),(4932,some (fanBlockRows 2180)),(4933,some (fanBlockRows 2181)),(4934,some (fanBlockRows 2182)),(4935,some (fanBlockRows 2183)),(4936,some (fanBlockRows 2184)),(4937,some (fanBlockRows 2185)),(4938,some (fanBlockRows 2186)),(4939,some (fanBlockRows 2187)),(4940,some (fanBlockRows 2188)),(4941,some (fanBlockRows 2189)),(4942,some (fanBlockRows 2190)),(4943,some (fanBlockRows 2191)),(4944,some (fanBlockRows 2192)),(4945,some (fanBlockRows 2193)),(4946,some (fanBlockRows 2194)),(4947,some (fanBlockRows 2195)),(4948,some (fanBlockRows 2196)),(4949,some (fanBlockRows 2197)),(4950,some (fanBlockRows 2198)),(4951,some (fanBlockRows 2199)),(4952,some (fanBlockRows 2200)),(4953,some (fanBlockRows 2201)),(4954,some (fanBlockRows 2202)),(4955,some (fanBlockRows 2203)),(4956,some (fanBlockRows 2204)),(4957,some (fanBlockRows 2205)),(4958,some (fanBlockRows 2206)),(4959,some (fanBlockRows 2207)),(4960,some (fanBlockRows 2208)),(4961,some (fanBlockRows 2209)),(4962,some (fanBlockRows 2210)),(4963,some (fanBlockRows 2211)),(4964,some (fanBlockRows 2212)),(4965,some (fanBlockRows 2214)),(4966,some (fanBlockRows 2215)),(4967,some (fanBlockRows 2216)),(4968,some (fanBlockRows 2217)),(4969,some (fanBlockRows 2218)),(4970,some (fanBlockRows 2219)),(4971,some (fanBlockRows 2220)),(4972,some (fanBlockRows 2221)),(4973,some (fanBlockRows 2222)),(4974,some (fanBlockRows 2223)),(4975,some (fanBlockRows 2116)),(4976,some (fanBlockRows 2117)),(4977,some (fanBlockRows 2118)),(4978,some (fanBlockRows 2119)),(4979,some (fanBlockRows 2120)),(4980,some (fanBlockRows 2121)),(4981,some (fanBlockRows 2122)),(4982,some (fanBlockRows 2123)),(4983,some (fanBlockRows 2124)),(4984,some (fanBlockRows 2125)),(4985,some (fanBlockRows 2127)),(4986,some (fanBlockRows 2128)),(4987,some (fanBlockRows 2129)),(4988,some (fanBlockRows 2130)),(4989,some (fanBlockRows 2131)),(4990,some (fanBlockRows 2132)),(4991,some (fanBlockRows 2133)),(4992,none),(4993,none),(4994,none),(4995,none),(4996,none),(4997,none),(4998,none),(4999,none),(5000,none),(5001,none),(5002,none)]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step04.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 113).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step04.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step04.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step04

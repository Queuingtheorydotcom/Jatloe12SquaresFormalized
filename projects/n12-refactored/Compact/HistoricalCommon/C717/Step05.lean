import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step05
import Compact.HistoricalCommon.C717.Step05Groups00
import Compact.HistoricalCommon.C717.Step05Groups01
import Compact.HistoricalCommon.C717.Step05Groups02
import Compact.HistoricalCommon.C717.Step05Groups03
import Compact.HistoricalCommon.C717.Step05Groups04
import Compact.HistoricalCommon.C717.Step05Groups05
import Compact.HistoricalCommon.C717.Step05Groups06
import Compact.HistoricalCommon.C717.Step05Groups07
import Compact.HistoricalCommon.C717.Step05Groups08

namespace N12Compact.HistoricalCommon.C717.Step05
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 49 (.neighborCut 16 (.sourceCut 24 .leaf .leaf) (.neighborCut 16 (.sourceCut 12 .leaf (.sourceCut 6 .leaf (.sourceCut 6 .leaf .leaf))) (.neighborCut 32 .leaf .leaf))) (.neighborCut 8 (.sourceCut 25 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.sourceCut 12 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 6 .leaf .leaf) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 6 .leaf .leaf))))) (.sourceCut 13 (.neighborCut 32 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))))) (.neighborCut 32 .leaf (.neighborCut 32 (.sourceCut 12 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf) (.neighborCut 16 (.sourceCut 12 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,99,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 99) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 99) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context5738_header,context5749_header,context5760_header,context5771_header,context5777_header,context5783_header,context5794_header,context5803_header,context5814_header,context5726_header,context5729_header,context5730_header,context5731_header,context5732_header,context5733_header,context5734_header,context5735_header,context5736_header,context5737_header,context5739_header,context5740_header,context5741_header,context5742_header,context5743_header,context5744_header,context5745_header,context5746_header,context5747_header,context5748_header,context5750_header,context5751_header,context5752_header,context5753_header,context5754_header,context5755_header,context5756_header,context5757_header,context5758_header,context5759_header,context5761_header,context5762_header,context5763_header,context5764_header,context5765_header,context5766_header,context5767_header,context5768_header,context5769_header,context5770_header,context5772_header,context5773_header,context5774_header,context5775_header,context5776_header,context5778_header,context5779_header,context5780_header,context5781_header,context5782_header,context5784_header,context5785_header,context5786_header,context5787_header,context5788_header,context5789_header,context5790_header,context5791_header,context5792_header,context5793_header,context5795_header,context5796_header,context5797_header,context5798_header,context5799_header,context5800_header,context5801_header,context5802_header,context5804_header,context5805_header,context5806_header,context5807_header,context5808_header,context5809_header,context5810_header,context5811_header,context5812_header,context5813_header,context5605_header,context5717_header,context5718_header,context5719_header,context5720_header,context5721_header,context5722_header,context5723_header,context5724_header,context5725_header,context5727_header,context5728_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 99).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5131,none),(5132,some (fanBlockRows 2247)),(5133,some (fanBlockRows 2258)),(5134,some (fanBlockRows 2269)),(5135,some (fanBlockRows 2280)),(5136,some (fanBlockRows 2286)),(5137,some (fanBlockRows 2292)),(5138,some (fanBlockRows 2303)),(5139,some (fanBlockRows 2312)),(5140,some (fanBlockRows 2323)),(5141,some (fanBlockRows 2235)),(5142,some (fanBlockRows 2238)),(5143,some (fanBlockRows 2239)),(5144,some (fanBlockRows 2240)),(5145,some (fanBlockRows 2241)),(5146,some (fanBlockRows 2242)),(5147,some (fanBlockRows 2243)),(5148,some (fanBlockRows 2244)),(5149,some (fanBlockRows 2245)),(5150,some (fanBlockRows 2246)),(5151,some (fanBlockRows 2248)),(5152,some (fanBlockRows 2249)),(5153,some (fanBlockRows 2250)),(5154,some (fanBlockRows 2251)),(5155,some (fanBlockRows 2252)),(5156,some (fanBlockRows 2253)),(5157,some (fanBlockRows 2254)),(5158,some (fanBlockRows 2255)),(5159,some (fanBlockRows 2256)),(5160,some (fanBlockRows 2257)),(5161,some (fanBlockRows 2259)),(5162,some (fanBlockRows 2260)),(5163,some (fanBlockRows 2261)),(5164,some (fanBlockRows 2262)),(5165,some (fanBlockRows 2263)),(5166,some (fanBlockRows 2264)),(5167,some (fanBlockRows 2265)),(5168,some (fanBlockRows 2266)),(5169,some (fanBlockRows 2267)),(5170,some (fanBlockRows 2268)),(5171,some (fanBlockRows 2270)),(5172,some (fanBlockRows 2271)),(5173,some (fanBlockRows 2272)),(5174,some (fanBlockRows 2273)),(5175,some (fanBlockRows 2274)),(5176,some (fanBlockRows 2275)),(5177,some (fanBlockRows 2276)),(5178,some (fanBlockRows 2277)),(5179,some (fanBlockRows 2278)),(5180,some (fanBlockRows 2279)),(5181,some (fanBlockRows 2281)),(5182,some (fanBlockRows 2282)),(5183,some (fanBlockRows 2283)),(5184,some (fanBlockRows 2284)),(5185,some (fanBlockRows 2285)),(5186,none),(5187,none),(5188,none),(5189,none),(5190,none),(5191,none),(5192,none),(5193,none),(5194,none),(5195,none),(5196,some (fanBlockRows 2287)),(5197,some (fanBlockRows 2288)),(5198,some (fanBlockRows 2289)),(5199,some (fanBlockRows 2290)),(5200,some (fanBlockRows 2291)),(5201,some (fanBlockRows 2293)),(5202,some (fanBlockRows 2294)),(5203,some (fanBlockRows 2295)),(5204,some (fanBlockRows 2296)),(5205,some (fanBlockRows 2297)),(5206,some (fanBlockRows 2298)),(5207,some (fanBlockRows 2299)),(5208,some (fanBlockRows 2300)),(5209,some (fanBlockRows 2301)),(5210,some (fanBlockRows 2302)),(5211,some (fanBlockRows 2304)),(5212,some (fanBlockRows 2305)),(5213,none),(5214,none),(5215,some (fanBlockRows 2306)),(5216,some (fanBlockRows 2307)),(5217,some (fanBlockRows 2308)),(5218,some (fanBlockRows 2309)),(5219,some (fanBlockRows 2310)),(5220,some (fanBlockRows 2311)),(5221,some (fanBlockRows 2313)),(5222,some (fanBlockRows 2314)),(5223,some (fanBlockRows 2315)),(5224,some (fanBlockRows 2316)),(5225,some (fanBlockRows 2317)),(5226,some (fanBlockRows 2318)),(5227,some (fanBlockRows 2319)),(5228,some (fanBlockRows 2320)),(5229,some (fanBlockRows 2321)),(5230,some (fanBlockRows 2322)),(5231,some (fanBlockRows 2225)),(5232,some (fanBlockRows 2226)),(5233,some (fanBlockRows 2227)),(5234,some (fanBlockRows 2228)),(5235,some (fanBlockRows 2229)),(5236,some (fanBlockRows 2230)),(5237,some (fanBlockRows 2231)),(5238,some (fanBlockRows 2232)),(5239,some (fanBlockRows 2233)),(5240,some (fanBlockRows 2234)),(5241,some (fanBlockRows 2236)),(5242,some (fanBlockRows 2237)),(5243,none),(5244,none),(5245,none),(5246,none),(5247,none),(5248,none),(5249,none),(5250,none),(5251,none),(5252,none),(5253,none),(5254,none),(5255,none),(5256,none),(5257,none),(5258,none)]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step05.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain0_1Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step05.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step05.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain0_1Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain0_1Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step05

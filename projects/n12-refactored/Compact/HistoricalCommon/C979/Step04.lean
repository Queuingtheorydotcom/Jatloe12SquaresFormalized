import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step04
import Compact.HistoricalCommon.C979.Step04Groups00
import Compact.HistoricalCommon.C979.Step04Groups01
import Compact.HistoricalCommon.C979.Step04Groups02
import Compact.HistoricalCommon.C979.Step04Groups03
import Compact.HistoricalCommon.C979.Step04Groups04
import Compact.HistoricalCommon.C979.Step04Groups05
import Compact.HistoricalCommon.C979.Step04Groups06
import Compact.HistoricalCommon.C979.Step04Groups07
import Compact.HistoricalCommon.C979.Step04Groups08
import Compact.HistoricalCommon.C979.Step04Groups09
import Compact.HistoricalCommon.C979.Step04Groups10

namespace N12Compact.HistoricalCommon.C979.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 28 (.neighborCut 14 (.sourceCut 14 .leaf .leaf) (.neighborCut 14 (.sourceCut 14 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 28 .leaf (.neighborCut 28 (.sourceCut 14 (.neighborCut 14 .leaf (.sourceCut 7 .leaf .leaf)) (.sourceCut 7 .leaf (.sourceCut 3 .leaf .leaf))) .leaf)))) (.sourceCut 7 (.neighborCut 28 .leaf (.neighborCut 28 .leaf (.neighborCut 28 .leaf .leaf))) (.sourceCut 7 (.neighborCut 28 .leaf (.neighborCut 28 .leaf (.neighborCut 28 .leaf .leaf))) (.sourceCut 15 (.neighborCut 14 .leaf (.neighborCut 14 .leaf (.neighborCut 28 .leaf (.neighborCut 28 (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 14 (.sourceCut 7 .leaf .leaf) .leaf))))) (.sourceCut 28 (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 28 .leaf .leaf)))) (.neighborCut 56 .leaf (.sourceCut 14 (.neighborCut 14 .leaf (.neighborCut 14 .leaf (.neighborCut 14 .leaf .leaf))) (.neighborCut 28 .leaf (.neighborCut 14 .leaf (.neighborCut 7 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,114,0,112⟩ scopes := by decide +kernel

theorem covered (i : Fin 114) (j : Fin 112) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 114) (j : Fin 112) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context12399_header,context12410_header,context12421_header,context12432_header,context12443_header,context12454_header,context12465_header,context12362_header,context12370_header,context12371_header,context12372_header,context12373_header,context12374_header,context12375_header,context12376_header,context12377_header,context12378_header,context12379_header,context12380_header,context12381_header,context12382_header,context12383_header,context12384_header,context12385_header,context12386_header,context12387_header,context12388_header,context12389_header,context12390_header,context12391_header,context12392_header,context12393_header,context12394_header,context12395_header,context12396_header,context12397_header,context12398_header,context12400_header,context12401_header,context12402_header,context12403_header,context12404_header,context12405_header,context12406_header,context12407_header,context12408_header,context12409_header,context12411_header,context12412_header,context12413_header,context12414_header,context12415_header,context12416_header,context12417_header,context12418_header,context12419_header,context12420_header,context12422_header,context12423_header,context12424_header,context12425_header,context12426_header,context12427_header,context12428_header,context12429_header,context12430_header,context12431_header,context12433_header,context12434_header,context12435_header,context12436_header,context12437_header,context12438_header,context12439_header,context12440_header,context12441_header,context12442_header,context12444_header,context12445_header,context12446_header,context12447_header,context12448_header,context12449_header,context12450_header,context12451_header,context12452_header,context12453_header,context12455_header,context12456_header,context12457_header,context12458_header,context12459_header,context12460_header,context12461_header,context12462_header,context12463_header,context12464_header,context12237_header,context12353_header,context12354_header,context12355_header,context12356_header,context12357_header,context12358_header,context12359_header,context12360_header,context12361_header,context12363_header,context12364_header,context12365_header,context12366_header,context12367_header,context12368_header,context12369_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 114).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11493,none),(11494,none),(11495,none),(11496,some (fanBlockRows 5235)),(11497,some (fanBlockRows 5236)),(11498,some (fanBlockRows 5246)),(11499,some (fanBlockRows 5257)),(11500,some (fanBlockRows 5268)),(11501,some (fanBlockRows 5279)),(11502,some (fanBlockRows 5290)),(11503,some (fanBlockRows 5221)),(11504,some (fanBlockRows 5229)),(11505,some (fanBlockRows 5230)),(11506,some (fanBlockRows 5231)),(11507,some (fanBlockRows 5232)),(11508,some (fanBlockRows 5233)),(11509,some (fanBlockRows 5234)),(11510,some (fanBlockRows 59)),(11511,some (fanBlockRows 59)),(11512,some (fanBlockRows 59)),(11513,some (fanBlockRows 59)),(11514,some (fanBlockRows 59)),(11515,some (fanBlockRows 59)),(11516,some (fanBlockRows 59)),(11517,some (fanBlockRows 59)),(11518,some (fanBlockRows 59)),(11519,some (fanBlockRows 59)),(11520,some (fanBlockRows 59)),(11521,some (fanBlockRows 59)),(11522,some (fanBlockRows 59)),(11523,some (fanBlockRows 59)),(11524,some (fanBlockRows 59)),(11525,some (fanBlockRows 59)),(11526,some (fanBlockRows 59)),(11527,some (fanBlockRows 59)),(11528,some (fanBlockRows 59)),(11529,some (fanBlockRows 59)),(11530,some (fanBlockRows 59)),(11531,some (fanBlockRows 59)),(11532,some (fanBlockRows 59)),(11533,some (fanBlockRows 59)),(11534,some (fanBlockRows 59)),(11535,some (fanBlockRows 59)),(11536,some (fanBlockRows 59)),(11537,some (fanBlockRows 59)),(11538,some (fanBlockRows 59)),(11539,some (fanBlockRows 59)),(11540,some (fanBlockRows 59)),(11541,some (fanBlockRows 59)),(11542,some (fanBlockRows 59)),(11543,some (fanBlockRows 59)),(11544,some (fanBlockRows 5237)),(11545,some (fanBlockRows 5238)),(11546,some (fanBlockRows 5239)),(11547,some (fanBlockRows 5240)),(11548,some (fanBlockRows 5241)),(11549,some (fanBlockRows 5242)),(11550,some (fanBlockRows 5243)),(11551,some (fanBlockRows 5244)),(11552,some (fanBlockRows 5245)),(11553,some (fanBlockRows 5247)),(11554,some (fanBlockRows 5248)),(11555,some (fanBlockRows 5249)),(11556,some (fanBlockRows 5250)),(11557,some (fanBlockRows 5251)),(11558,some (fanBlockRows 5252)),(11559,some (fanBlockRows 5253)),(11560,some (fanBlockRows 5254)),(11561,some (fanBlockRows 5255)),(11562,some (fanBlockRows 5256)),(11563,some (fanBlockRows 5258)),(11564,some (fanBlockRows 5259)),(11565,some (fanBlockRows 5260)),(11566,some (fanBlockRows 5261)),(11567,some (fanBlockRows 5262)),(11568,some (fanBlockRows 5263)),(11569,some (fanBlockRows 5264)),(11570,some (fanBlockRows 5265)),(11571,some (fanBlockRows 5266)),(11572,some (fanBlockRows 5267)),(11573,some (fanBlockRows 5269)),(11574,some (fanBlockRows 5270)),(11575,some (fanBlockRows 5271)),(11576,some (fanBlockRows 5272)),(11577,some (fanBlockRows 5273)),(11578,some (fanBlockRows 5274)),(11579,some (fanBlockRows 5275)),(11580,some (fanBlockRows 5276)),(11581,some (fanBlockRows 5277)),(11582,some (fanBlockRows 5278)),(11583,some (fanBlockRows 5280)),(11584,some (fanBlockRows 5281)),(11585,some (fanBlockRows 5282)),(11586,some (fanBlockRows 5283)),(11587,some (fanBlockRows 5284)),(11588,some (fanBlockRows 5285)),(11589,some (fanBlockRows 5286)),(11590,some (fanBlockRows 5287)),(11591,some (fanBlockRows 5288)),(11592,some (fanBlockRows 5289)),(11593,some (fanBlockRows 5211)),(11594,some (fanBlockRows 5212)),(11595,some (fanBlockRows 5213)),(11596,some (fanBlockRows 5214)),(11597,some (fanBlockRows 5215)),(11598,some (fanBlockRows 5216)),(11599,some (fanBlockRows 5217)),(11600,some (fanBlockRows 5218)),(11601,some (fanBlockRows 5219)),(11602,some (fanBlockRows 5220)),(11603,some (fanBlockRows 5222)),(11604,some (fanBlockRows 5223)),(11605,some (fanBlockRows 5224)),(11606,some (fanBlockRows 5225)),(11607,some (fanBlockRows 5226)),(11608,some (fanBlockRows 5227)),(11609,some (fanBlockRows 5228)),(11610,none),(11611,none),(11612,none),(11613,none),(11614,none),(11615,none),(11616,none),(11617,none),(11618,none),(11619,none),(11620,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step04.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 112).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain5_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step04.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step04.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain5_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain5_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step04

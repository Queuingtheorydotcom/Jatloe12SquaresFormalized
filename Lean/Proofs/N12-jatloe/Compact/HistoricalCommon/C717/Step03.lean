import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step03
import Compact.HistoricalCommon.C717.Step03Groups00
import Compact.HistoricalCommon.C717.Step03Groups01
import Compact.HistoricalCommon.C717.Step03Groups02
import Compact.HistoricalCommon.C717.Step03Groups03
import Compact.HistoricalCommon.C717.Step03Groups04
import Compact.HistoricalCommon.C717.Step03Groups05
import Compact.HistoricalCommon.C717.Step03Groups06
import Compact.HistoricalCommon.C717.Step03Groups07
import Compact.HistoricalCommon.C717.Step03Groups08
import Compact.HistoricalCommon.C717.Step03Groups09
import Compact.HistoricalCommon.C717.Step03Groups10
import Compact.HistoricalCommon.C717.Step03Groups11
import Compact.HistoricalCommon.C717.Step03Groups12

namespace N12Compact.HistoricalCommon.C717.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44,group45,group46,group47,group48,group49,group50]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope,group45_scope,group46_scope,group47_scope,group48_scope,group49_scope,group50_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 54 (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 14 (.neighborCut 8 .leaf .leaf) (.sourceCut 13 .leaf .leaf))) (.neighborCut 16 .leaf (.sourceCut 27 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 16 .leaf (.neighborCut 16 .leaf .leaf)) (.neighborCut 16 (.sourceCut 7 .leaf .leaf) (.neighborCut 16 .leaf .leaf))))) (.neighborCut 16 (.sourceCut 13 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf)))))))) (.sourceCut 27 (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 16 (.sourceCut 13 .leaf .leaf) (.neighborCut 16 (.sourceCut 13 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))))) (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 13 .leaf .leaf) (.neighborCut 16 (.sourceCut 6 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 8 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,108,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 108) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 108) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context5260_header,context5427_header,context5438_header,context5449_header,context5453_header,context5454_header,context5462_header,context5473_header,context5484_header,context5495_header,context5399_header,context5410_header,context5419_header,context5420_header,context5421_header,context5422_header,context5423_header,context5424_header,context5425_header,context5426_header,context5428_header,context5429_header,context5430_header,context5431_header,context5432_header,context5433_header,context5434_header,context5435_header,context5436_header,context5437_header,context5439_header,context5440_header,context5441_header,context5442_header,context5443_header,context5444_header,context5445_header,context5446_header,context5447_header,context5448_header,context5450_header,context5451_header,context5452_header,context5455_header,context5456_header,context5457_header,context5458_header,context5459_header,context5460_header,context5461_header,context5463_header,context5464_header,context5465_header,context5466_header,context5467_header,context5468_header,context5469_header,context5470_header,context5471_header,context5472_header,context5474_header,context5475_header,context5476_header,context5477_header,context5478_header,context5479_header,context5480_header,context5481_header,context5482_header,context5483_header,context5485_header,context5486_header,context5487_header,context5488_header,context5489_header,context5490_header,context5491_header,context5492_header,context5493_header,context5494_header,context5389_header,context5390_header,context5391_header,context5392_header,context5393_header,context5394_header,context5395_header,context5396_header,context5397_header,context5398_header,context5400_header,context5401_header,context5402_header,context5403_header,context5404_header,context5405_header,context5406_header,context5407_header,context5408_header,context5409_header,context5411_header,context5412_header,context5413_header,context5414_header,context5415_header,context5416_header,context5417_header,context5418_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 108).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(4499,some (fanBlockRows 2008)),(4500,some (fanBlockRows 2047)),(4501,some (fanBlockRows 2058)),(4502,some (fanBlockRows 2069)),(4503,some (fanBlockRows 2073)),(4504,some (fanBlockRows 2074)),(4505,some (fanBlockRows 2082)),(4506,some (fanBlockRows 2093)),(4507,some (fanBlockRows 2104)),(4508,some (fanBlockRows 2115)),(4509,some (fanBlockRows 2019)),(4510,some (fanBlockRows 2030)),(4511,some (fanBlockRows 2039)),(4512,some (fanBlockRows 2040)),(4513,some (fanBlockRows 2041)),(4514,some (fanBlockRows 2042)),(4515,some (fanBlockRows 2043)),(4516,some (fanBlockRows 2044)),(4517,some (fanBlockRows 2045)),(4518,some (fanBlockRows 2046)),(4519,some (fanBlockRows 2048)),(4520,some (fanBlockRows 2049)),(4521,some (fanBlockRows 2050)),(4522,some (fanBlockRows 2051)),(4523,some (fanBlockRows 2052)),(4524,some (fanBlockRows 2053)),(4525,some (fanBlockRows 2054)),(4526,some (fanBlockRows 2055)),(4527,some (fanBlockRows 2056)),(4528,some (fanBlockRows 2057)),(4529,some (fanBlockRows 2059)),(4530,some (fanBlockRows 2060)),(4531,some (fanBlockRows 2061)),(4532,some (fanBlockRows 2062)),(4533,some (fanBlockRows 2063)),(4534,some (fanBlockRows 2064)),(4535,some (fanBlockRows 2065)),(4536,some (fanBlockRows 2066)),(4537,some (fanBlockRows 2067)),(4538,some (fanBlockRows 2068)),(4539,some (fanBlockRows 2070)),(4540,some (fanBlockRows 2071)),(4541,some (fanBlockRows 2072)),(4542,none),(4543,none),(4544,none),(4545,none),(4546,none),(4547,none),(4548,none),(4549,none),(4550,none),(4551,none),(4552,none),(4553,none),(4554,none),(4555,none),(4556,none),(4557,none),(4558,none),(4559,none),(4560,none),(4561,none),(4562,some (fanBlockRows 2075)),(4563,some (fanBlockRows 2076)),(4564,some (fanBlockRows 2077)),(4565,some (fanBlockRows 2078)),(4566,some (fanBlockRows 2079)),(4567,some (fanBlockRows 2080)),(4568,some (fanBlockRows 2081)),(4569,some (fanBlockRows 2083)),(4570,some (fanBlockRows 2084)),(4571,some (fanBlockRows 2085)),(4572,some (fanBlockRows 2086)),(4573,some (fanBlockRows 2087)),(4574,some (fanBlockRows 2088)),(4575,some (fanBlockRows 2089)),(4576,some (fanBlockRows 2090)),(4577,some (fanBlockRows 2091)),(4578,some (fanBlockRows 2092)),(4579,some (fanBlockRows 2094)),(4580,some (fanBlockRows 2095)),(4581,some (fanBlockRows 2096)),(4582,some (fanBlockRows 2097)),(4583,some (fanBlockRows 2098)),(4584,some (fanBlockRows 2099)),(4585,some (fanBlockRows 2100)),(4586,some (fanBlockRows 2101)),(4587,some (fanBlockRows 2102)),(4588,some (fanBlockRows 2103)),(4589,some (fanBlockRows 2105)),(4590,some (fanBlockRows 2106)),(4591,some (fanBlockRows 2107)),(4592,some (fanBlockRows 2108)),(4593,some (fanBlockRows 2109)),(4594,some (fanBlockRows 2110)),(4595,some (fanBlockRows 2111)),(4596,some (fanBlockRows 2112)),(4597,some (fanBlockRows 2113)),(4598,some (fanBlockRows 2114)),(4599,some (fanBlockRows 2009)),(4600,some (fanBlockRows 2010)),(4601,some (fanBlockRows 2011)),(4602,some (fanBlockRows 2012)),(4603,some (fanBlockRows 2013)),(4604,some (fanBlockRows 2014)),(4605,some (fanBlockRows 2015)),(4606,some (fanBlockRows 2016)),(4607,some (fanBlockRows 2017)),(4608,some (fanBlockRows 2018)),(4609,some (fanBlockRows 2020)),(4610,some (fanBlockRows 2021)),(4611,some (fanBlockRows 2022)),(4612,some (fanBlockRows 2023)),(4613,some (fanBlockRows 2024)),(4614,some (fanBlockRows 2025)),(4615,some (fanBlockRows 2026)),(4616,some (fanBlockRows 2027)),(4617,some (fanBlockRows 2028)),(4618,some (fanBlockRows 2029)),(4619,some (fanBlockRows 2031)),(4620,some (fanBlockRows 2032)),(4621,some (fanBlockRows 2033)),(4622,some (fanBlockRows 2034)),(4623,some (fanBlockRows 2035)),(4624,some (fanBlockRows 2036)),(4625,some (fanBlockRows 2037)),(4626,some (fanBlockRows 2038))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step03.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain4_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step03.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step03.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain4_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain4_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step03

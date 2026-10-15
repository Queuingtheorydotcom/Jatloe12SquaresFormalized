import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step00
import Compact.HistoricalCommon.C979.Step00Groups00
import Compact.HistoricalCommon.C979.Step00Groups01
import Compact.HistoricalCommon.C979.Step00Groups02
import Compact.HistoricalCommon.C979.Step00Groups03
import Compact.HistoricalCommon.C979.Step00Groups04
import Compact.HistoricalCommon.C979.Step00Groups05
import Compact.HistoricalCommon.C979.Step00Groups06

namespace N12Compact.HistoricalCommon.C979.Step00
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
  [context5117_header,context5128_header,context5030_header,context5038_header,context5039_header,context5040_header,context5041_header,context5042_header,context5043_header,context5044_header,context5045_header,context5046_header,context5047_header,context5048_header,context5049_header,context5050_header,context5051_header,context5052_header,context5053_header,context5054_header,context5055_header,context5056_header,context5057_header,context5058_header,context5059_header,context5060_header,context5061_header,context5062_header,context5063_header,context5064_header,context5065_header,context5066_header,context5067_header,context5068_header,context5069_header,context5070_header,context5071_header,context5072_header,context5073_header,context5074_header,context5075_header,context5076_header,context5077_header,context5078_header,context5079_header,context5080_header,context5081_header,context5082_header,context5083_header,context5084_header,context5085_header,context5086_header,context5087_header,context5088_header,context5089_header,context5090_header,context5091_header,context5092_header,context9747_header,context9748_header,context9749_header,context9750_header,context9751_header,context9752_header,context9753_header,context9754_header,context9755_header,context5102_header,context5103_header,context5104_header,context5105_header,context5106_header,context5107_header,context5108_header,context5109_header,context5110_header,context5111_header,context5112_header,context5113_header,context5114_header,context5115_header,context5116_header,context5118_header,context5119_header,context5120_header,context5121_header,context5122_header,context5123_header,context5124_header,context5125_header,context5126_header,context5127_header,context5017_header,context5021_header,context5022_header,context5023_header,context5024_header,context5025_header,context5026_header,context5027_header,context5028_header,context5029_header,context5031_header,context5032_header,context5033_header,context5034_header,context5035_header,context5036_header,context5037_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 109).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2422,none),(2423,none),(2424,none),(2425,none),(2426,none),(2427,none),(2428,none),(2429,none),(2430,some (fanBlockRows 974)),(2431,some (fanBlockRows 985)),(2432,some (fanBlockRows 939)),(2433,some (fanBlockRows 940)),(2434,some (fanBlockRows 941)),(2435,some (fanBlockRows 942)),(2436,some (fanBlockRows 943)),(2437,some (fanBlockRows 944)),(2438,some (fanBlockRows 945)),(2439,some (fanBlockRows 1852)),(2440,some (fanBlockRows 1853)),(2441,some (fanBlockRows 1854)),(2442,some (fanBlockRows 1855)),(2443,some (fanBlockRows 1856)),(2444,some (fanBlockRows 1857)),(2445,some (fanBlockRows 1858)),(2446,some (fanBlockRows 1859)),(2447,some (fanBlockRows 1860)),(2448,some (fanBlockRows 1861)),(2449,some (fanBlockRows 1862)),(2450,some (fanBlockRows 1863)),(2451,some (fanBlockRows 1864)),(2452,some (fanBlockRows 1865)),(2453,some (fanBlockRows 1866)),(2454,some (fanBlockRows 1867)),(2455,some (fanBlockRows 1868)),(2456,some (fanBlockRows 1869)),(2457,some (fanBlockRows 1870)),(2458,some (fanBlockRows 1871)),(2459,some (fanBlockRows 1872)),(2460,some (fanBlockRows 1873)),(2461,some (fanBlockRows 1874)),(2462,some (fanBlockRows 1875)),(2463,some (fanBlockRows 1876)),(2464,some (fanBlockRows 1877)),(2465,some (fanBlockRows 1878)),(2466,some (fanBlockRows 1879)),(2467,some (fanBlockRows 1880)),(2468,some (fanBlockRows 1881)),(2469,some (fanBlockRows 1882)),(2470,some (fanBlockRows 1883)),(2471,some (fanBlockRows 1884)),(2472,some (fanBlockRows 1885)),(2473,some (fanBlockRows 1886)),(2474,some (fanBlockRows 1887)),(2475,some (fanBlockRows 1888)),(2476,some (fanBlockRows 1889)),(2477,some (fanBlockRows 1890)),(2478,some (fanBlockRows 1891)),(2479,some (fanBlockRows 1892)),(2480,some (fanBlockRows 1893)),(2481,some (fanBlockRows 1894)),(2482,some (fanBlockRows 1895)),(2483,some (fanBlockRows 1896)),(2484,some (fanBlockRows 1897)),(2485,some (fanBlockRows 1898)),(2486,some (fanBlockRows 1899)),(2487,some (fanBlockRows 1900)),(2488,some (fanBlockRows 4111)),(2489,some (fanBlockRows 4112)),(2490,some (fanBlockRows 4113)),(2491,some (fanBlockRows 4114)),(2492,some (fanBlockRows 4115)),(2493,some (fanBlockRows 4116)),(2494,some (fanBlockRows 4117)),(2495,some (fanBlockRows 4118)),(2496,some (fanBlockRows 4119)),(2497,some (fanBlockRows 1910)),(2498,some (fanBlockRows 1911)),(2499,some (fanBlockRows 1912)),(2500,some (fanBlockRows 1913)),(2501,some (fanBlockRows 955)),(2502,some (fanBlockRows 956)),(2503,some (fanBlockRows 957)),(2504,some (fanBlockRows 958)),(2505,some (fanBlockRows 959)),(2506,some (fanBlockRows 960)),(2507,some (fanBlockRows 961)),(2508,some (fanBlockRows 962)),(2509,some (fanBlockRows 963)),(2510,some (fanBlockRows 964)),(2511,some (fanBlockRows 965)),(2512,some (fanBlockRows 966)),(2513,some (fanBlockRows 967)),(2514,some (fanBlockRows 968)),(2515,some (fanBlockRows 969)),(2516,some (fanBlockRows 970)),(2517,some (fanBlockRows 971)),(2518,some (fanBlockRows 972)),(2519,some (fanBlockRows 973)),(2520,some (fanBlockRows 975)),(2521,some (fanBlockRows 976)),(2522,some (fanBlockRows 977)),(2523,some (fanBlockRows 978)),(2524,some (fanBlockRows 979)),(2525,some (fanBlockRows 980)),(2526,some (fanBlockRows 981)),(2527,some (fanBlockRows 982)),(2528,some (fanBlockRows 983)),(2529,some (fanBlockRows 984)),(2530,some (fanBlockRows 930)),(2531,some (fanBlockRows 931)),(2532,some (fanBlockRows 932)),(2533,some (fanBlockRows 933)),(2534,some (fanBlockRows 934)),(2535,some (fanBlockRows 935)),(2536,some (fanBlockRows 936)),(2537,some (fanBlockRows 937)),(2538,some (fanBlockRows 938)),(2539,none),(2540,none),(2541,none),(2542,none),(2543,none),(2544,none),(2545,none),(2546,none),(2547,none),(2548,none),(2549,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step00.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 113).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain8_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step00.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step00.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain8_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain8_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step00

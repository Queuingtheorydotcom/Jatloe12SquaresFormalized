import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step01
import Compact.HistoricalCommon.C713.Step01Groups00
import Compact.HistoricalCommon.C713.Step01Groups01
import Compact.HistoricalCommon.C713.Step01Groups02
import Compact.HistoricalCommon.C713.Step01Groups03
import Compact.HistoricalCommon.C713.Step01Groups04
import Compact.HistoricalCommon.C713.Step01Groups05
import Compact.HistoricalCommon.C713.Step01Groups06

namespace N12Compact.HistoricalCommon.C713.Step01
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
  (.sourceCut 64 (.neighborCut 32 (.sourceCut 16 (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.sourceCut 16 .leaf (.neighborCut 16 (.sourceCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf))) (.neighborCut 32 .leaf (.sourceCut 32 (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf)) .leaf)) .leaf))) (.neighborCut 32 (.sourceCut 32 (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)) (.sourceCut 16 (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf)) .leaf)) (.neighborCut 32 .leaf (.sourceCut 32 .leaf (.neighborCut 32 .leaf (.sourceCut 16 .leaf (.neighborCut 16 .leaf .leaf)))))))

theorem partition_checked : partition.Check ⟨0,128,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context2063_header,context2230_header,context2249_header,context2260_header,context2271_header,context2282_header,context2293_header,context2304_header,context2315_header,context2326_header,context2202_header,context2213_header,context2222_header,context2223_header,context2224_header,context2225_header,context2226_header,context2227_header,context2228_header,context2229_header,context2231_header,context2232_header,context2234_header,context2236_header,context2238_header,context2240_header,context2242_header,context2244_header,context2246_header,context2248_header,context2250_header,context2251_header,context2252_header,context2253_header,context2254_header,context2255_header,context2256_header,context2257_header,context2258_header,context2259_header,context2261_header,context2262_header,context2263_header,context2264_header,context2265_header,context2266_header,context2267_header,context2268_header,context2269_header,context2270_header,context2272_header,context2273_header,context2274_header,context2275_header,context2276_header,context2277_header,context2278_header,context2279_header,context2280_header,context2281_header,context2283_header,context2284_header,context2285_header,context2286_header,context2287_header,context2288_header,context2289_header,context2290_header,context2291_header,context2292_header,context2294_header,context2295_header,context2296_header,context2297_header,context2298_header,context2299_header,context2300_header,context2301_header,context2302_header,context2303_header,context2305_header,context2306_header,context2307_header,context2308_header,context2309_header,context2310_header,context2311_header,context2312_header,context2313_header,context2314_header,context2316_header,context2317_header,context2318_header,context2319_header,context2320_header,context2321_header,context2322_header,context2323_header,context2324_header,context2325_header,context2192_header,context2193_header,context2194_header,context2195_header,context2196_header,context2197_header,context2198_header,context2199_header,context2200_header,context2201_header,context2203_header,context2204_header,context2205_header,context2206_header,context2207_header,context2208_header,context2209_header,context2210_header,context2211_header,context2212_header,context2214_header,context2215_header,context2216_header,context2217_header,context2218_header,context2219_header,context2220_header,context2221_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2422,some (fanBlockRows 810)),(2423,some (fanBlockRows 849)),(2424,some (fanBlockRows 852)),(2425,some (fanBlockRows 863)),(2426,some (fanBlockRows 874)),(2427,some (fanBlockRows 885)),(2428,some (fanBlockRows 896)),(2429,some (fanBlockRows 907)),(2430,some (fanBlockRows 918)),(2431,some (fanBlockRows 929)),(2432,some (fanBlockRows 821)),(2433,some (fanBlockRows 832)),(2434,some (fanBlockRows 841)),(2435,some (fanBlockRows 842)),(2436,some (fanBlockRows 843)),(2437,some (fanBlockRows 844)),(2438,some (fanBlockRows 845)),(2439,some (fanBlockRows 846)),(2440,some (fanBlockRows 847)),(2441,some (fanBlockRows 848)),(2442,some (fanBlockRows 850)),(2443,some (fanBlockRows 851)),(2444,some (fanBlockRows 59)),(2445,some (fanBlockRows 59)),(2446,some (fanBlockRows 59)),(2447,some (fanBlockRows 59)),(2448,some (fanBlockRows 59)),(2449,some (fanBlockRows 59)),(2450,some (fanBlockRows 59)),(2451,some (fanBlockRows 59)),(2452,some (fanBlockRows 853)),(2453,some (fanBlockRows 854)),(2454,some (fanBlockRows 855)),(2455,some (fanBlockRows 856)),(2456,some (fanBlockRows 857)),(2457,some (fanBlockRows 858)),(2458,some (fanBlockRows 859)),(2459,some (fanBlockRows 860)),(2460,some (fanBlockRows 861)),(2461,some (fanBlockRows 862)),(2462,some (fanBlockRows 864)),(2463,some (fanBlockRows 865)),(2464,some (fanBlockRows 866)),(2465,some (fanBlockRows 867)),(2466,some (fanBlockRows 868)),(2467,some (fanBlockRows 869)),(2468,some (fanBlockRows 870)),(2469,some (fanBlockRows 871)),(2470,some (fanBlockRows 872)),(2471,some (fanBlockRows 873)),(2472,some (fanBlockRows 875)),(2473,some (fanBlockRows 876)),(2474,some (fanBlockRows 877)),(2475,some (fanBlockRows 878)),(2476,some (fanBlockRows 879)),(2477,some (fanBlockRows 880)),(2478,some (fanBlockRows 881)),(2479,some (fanBlockRows 882)),(2480,some (fanBlockRows 883)),(2481,some (fanBlockRows 884)),(2482,some (fanBlockRows 886)),(2483,some (fanBlockRows 887)),(2484,some (fanBlockRows 888)),(2485,some (fanBlockRows 889)),(2486,some (fanBlockRows 890)),(2487,some (fanBlockRows 891)),(2488,some (fanBlockRows 892)),(2489,some (fanBlockRows 893)),(2490,some (fanBlockRows 894)),(2491,some (fanBlockRows 895)),(2492,some (fanBlockRows 897)),(2493,some (fanBlockRows 898)),(2494,some (fanBlockRows 899)),(2495,some (fanBlockRows 900)),(2496,some (fanBlockRows 901)),(2497,some (fanBlockRows 902)),(2498,some (fanBlockRows 903)),(2499,some (fanBlockRows 904)),(2500,some (fanBlockRows 905)),(2501,some (fanBlockRows 906)),(2502,some (fanBlockRows 908)),(2503,some (fanBlockRows 909)),(2504,some (fanBlockRows 910)),(2505,some (fanBlockRows 911)),(2506,some (fanBlockRows 912)),(2507,some (fanBlockRows 913)),(2508,some (fanBlockRows 914)),(2509,some (fanBlockRows 915)),(2510,some (fanBlockRows 916)),(2511,some (fanBlockRows 917)),(2512,some (fanBlockRows 919)),(2513,some (fanBlockRows 920)),(2514,some (fanBlockRows 921)),(2515,some (fanBlockRows 922)),(2516,some (fanBlockRows 923)),(2517,some (fanBlockRows 924)),(2518,some (fanBlockRows 925)),(2519,some (fanBlockRows 926)),(2520,some (fanBlockRows 927)),(2521,some (fanBlockRows 928)),(2522,some (fanBlockRows 811)),(2523,some (fanBlockRows 812)),(2524,some (fanBlockRows 813)),(2525,some (fanBlockRows 814)),(2526,some (fanBlockRows 815)),(2527,some (fanBlockRows 816)),(2528,some (fanBlockRows 817)),(2529,some (fanBlockRows 818)),(2530,some (fanBlockRows 819)),(2531,some (fanBlockRows 820)),(2532,some (fanBlockRows 822)),(2533,some (fanBlockRows 823)),(2534,some (fanBlockRows 824)),(2535,some (fanBlockRows 825)),(2536,some (fanBlockRows 826)),(2537,some (fanBlockRows 827)),(2538,some (fanBlockRows 828)),(2539,some (fanBlockRows 829)),(2540,some (fanBlockRows 830)),(2541,some (fanBlockRows 831)),(2542,some (fanBlockRows 833)),(2543,some (fanBlockRows 834)),(2544,some (fanBlockRows 835)),(2545,some (fanBlockRows 836)),(2546,some (fanBlockRows 837)),(2547,some (fanBlockRows 838)),(2548,some (fanBlockRows 839)),(2549,some (fanBlockRows 840))]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step01.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain0_1Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step01.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step01.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain0_1Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain0_1Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step01

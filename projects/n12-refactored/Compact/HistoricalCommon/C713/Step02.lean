import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step02
import Compact.HistoricalCommon.C713.Step02Groups00
import Compact.HistoricalCommon.C713.Step02Groups01
import Compact.HistoricalCommon.C713.Step02Groups02
import Compact.HistoricalCommon.C713.Step02Groups03
import Compact.HistoricalCommon.C713.Step02Groups04
import Compact.HistoricalCommon.C713.Step02Groups05
import Compact.HistoricalCommon.C713.Step02Groups06
import Compact.HistoricalCommon.C713.Step02Groups07
import Compact.HistoricalCommon.C713.Step02Groups08
import Compact.HistoricalCommon.C713.Step02Groups09

namespace N12Compact.HistoricalCommon.C713.Step02
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 28 (.sourceCut 25 (.neighborCut 14 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) .leaf) (.sourceCut 25 .leaf (.sourceCut 25 (.neighborCut 14 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) .leaf) .leaf))) (.neighborCut 28 .leaf (.sourceCut 12 (.neighborCut 28 .leaf (.neighborCut 14 .leaf .leaf)) (.sourceCut 13 (.neighborCut 28 .leaf (.sourceCut 6 (.neighborCut 14 .leaf .leaf) (.neighborCut 14 .leaf .leaf))) (.sourceCut 12 (.neighborCut 28 .leaf .leaf) (.sourceCut 13 (.neighborCut 28 .leaf .leaf) (.sourceCut 25 (.neighborCut 14 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) (.neighborCut 14 .leaf (.neighborCut 14 .leaf (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf))))) (.neighborCut 14 .leaf (.neighborCut 14 (.sourceCut 13 .leaf .leaf) (.neighborCut 14 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf))))))))))))

theorem partition_checked : partition.Check ⟨0,101,0,113⟩ scopes := by decide +kernel

theorem covered (i : Fin 101) (j : Fin 113) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 101) (j : Fin 113) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context2538_header,context2549_header,context2458_header,context2459_header,context2460_header,context2461_header,context2462_header,context2463_header,context2464_header,context2465_header,context2466_header,context2467_header,context2468_header,context2469_header,context2470_header,context2471_header,context2472_header,context2473_header,context2474_header,context2475_header,context2476_header,context2477_header,context2478_header,context2479_header,context2480_header,context2481_header,context2482_header,context2483_header,context2484_header,context2485_header,context2486_header,context2487_header,context2488_header,context2489_header,context2490_header,context2491_header,context2492_header,context2493_header,context2494_header,context2495_header,context2496_header,context2497_header,context2498_header,context2499_header,context2500_header,context2501_header,context2502_header,context2503_header,context2504_header,context2505_header,context2506_header,context2507_header,context2508_header,context2509_header,context2510_header,context2511_header,context2512_header,context2513_header,context2514_header,context2515_header,context2516_header,context2517_header,context2518_header,context2519_header,context2520_header,context2521_header,context2522_header,context2523_header,context2524_header,context2525_header,context2526_header,context2527_header,context2528_header,context2529_header,context2530_header,context2531_header,context2532_header,context2533_header,context2534_header,context2535_header,context2536_header,context2537_header,context2539_header,context2540_header,context2541_header,context2542_header,context2543_header,context2544_header,context2545_header,context2546_header,context2547_header,context2548_header,context2327_header,context2450_header,context2451_header,context2452_header,context2453_header,context2454_header,context2455_header,context2456_header,context2457_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 101).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2550,none),(2551,none),(2552,none),(2553,none),(2554,none),(2555,none),(2556,none),(2557,none),(2558,some (fanBlockRows 974)),(2559,some (fanBlockRows 985)),(2560,some (fanBlockRows 939)),(2561,some (fanBlockRows 940)),(2562,some (fanBlockRows 941)),(2563,some (fanBlockRows 942)),(2564,some (fanBlockRows 943)),(2565,some (fanBlockRows 944)),(2566,some (fanBlockRows 945)),(2567,some (fanBlockRows 946)),(2568,some (fanBlockRows 947)),(2569,some (fanBlockRows 948)),(2570,some (fanBlockRows 949)),(2571,some (fanBlockRows 950)),(2572,some (fanBlockRows 59)),(2573,some (fanBlockRows 59)),(2574,some (fanBlockRows 59)),(2575,some (fanBlockRows 59)),(2576,some (fanBlockRows 59)),(2577,some (fanBlockRows 59)),(2578,some (fanBlockRows 59)),(2579,some (fanBlockRows 59)),(2580,some (fanBlockRows 59)),(2581,some (fanBlockRows 59)),(2582,some (fanBlockRows 59)),(2583,some (fanBlockRows 59)),(2584,some (fanBlockRows 59)),(2585,some (fanBlockRows 59)),(2586,some (fanBlockRows 59)),(2587,some (fanBlockRows 59)),(2588,some (fanBlockRows 59)),(2589,some (fanBlockRows 59)),(2590,some (fanBlockRows 59)),(2591,some (fanBlockRows 59)),(2592,some (fanBlockRows 59)),(2593,some (fanBlockRows 59)),(2594,some (fanBlockRows 59)),(2595,some (fanBlockRows 59)),(2596,some (fanBlockRows 59)),(2597,some (fanBlockRows 59)),(2598,some (fanBlockRows 59)),(2599,some (fanBlockRows 59)),(2600,some (fanBlockRows 59)),(2601,some (fanBlockRows 59)),(2602,some (fanBlockRows 59)),(2603,some (fanBlockRows 59)),(2604,some (fanBlockRows 59)),(2605,some (fanBlockRows 59)),(2606,some (fanBlockRows 59)),(2607,some (fanBlockRows 59)),(2608,some (fanBlockRows 59)),(2609,some (fanBlockRows 59)),(2610,some (fanBlockRows 59)),(2611,some (fanBlockRows 59)),(2612,some (fanBlockRows 59)),(2613,some (fanBlockRows 59)),(2614,some (fanBlockRows 59)),(2615,some (fanBlockRows 59)),(2616,some (fanBlockRows 59)),(2617,some (fanBlockRows 951)),(2618,some (fanBlockRows 952)),(2619,some (fanBlockRows 953)),(2620,some (fanBlockRows 954)),(2621,some (fanBlockRows 955)),(2622,some (fanBlockRows 956)),(2623,some (fanBlockRows 957)),(2624,some (fanBlockRows 958)),(2625,some (fanBlockRows 959)),(2626,some (fanBlockRows 960)),(2627,some (fanBlockRows 961)),(2628,some (fanBlockRows 962)),(2629,some (fanBlockRows 963)),(2630,some (fanBlockRows 964)),(2631,some (fanBlockRows 965)),(2632,some (fanBlockRows 966)),(2633,some (fanBlockRows 967)),(2634,some (fanBlockRows 968)),(2635,some (fanBlockRows 969)),(2636,some (fanBlockRows 970)),(2637,some (fanBlockRows 971)),(2638,some (fanBlockRows 972)),(2639,some (fanBlockRows 973)),(2640,some (fanBlockRows 975)),(2641,some (fanBlockRows 976)),(2642,some (fanBlockRows 977)),(2643,some (fanBlockRows 978)),(2644,some (fanBlockRows 979)),(2645,some (fanBlockRows 980)),(2646,some (fanBlockRows 981)),(2647,some (fanBlockRows 982)),(2648,some (fanBlockRows 983)),(2649,some (fanBlockRows 984)),(2650,some (fanBlockRows 930)),(2651,some (fanBlockRows 931)),(2652,some (fanBlockRows 932)),(2653,some (fanBlockRows 933)),(2654,some (fanBlockRows 934)),(2655,some (fanBlockRows 935)),(2656,some (fanBlockRows 936)),(2657,some (fanBlockRows 937)),(2658,some (fanBlockRows 938)),(2659,none),(2660,none),(2661,none),(2662,none),(2663,none),(2664,none),(2665,none),(2666,none),(2667,none),(2668,none),(2669,none)]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step02.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 113).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain8_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step02.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step02.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain8_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain8_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step02

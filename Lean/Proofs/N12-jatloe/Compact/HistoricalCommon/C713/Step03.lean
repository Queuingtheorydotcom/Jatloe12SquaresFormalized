import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step03
import Compact.HistoricalCommon.C713.Step03Groups00
import Compact.HistoricalCommon.C713.Step03Groups01
import Compact.HistoricalCommon.C713.Step03Groups02
import Compact.HistoricalCommon.C713.Step03Groups03
import Compact.HistoricalCommon.C713.Step03Groups04
import Compact.HistoricalCommon.C713.Step03Groups05
import Compact.HistoricalCommon.C713.Step03Groups06
import Compact.HistoricalCommon.C713.Step03Groups07
import Compact.HistoricalCommon.C713.Step03Groups08

namespace N12Compact.HistoricalCommon.C713.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 28 (.sourceCut 16 (.neighborCut 14 .leaf (.sourceCut 8 .leaf .leaf)) .leaf) (.neighborCut 14 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 15 .leaf (.neighborCut 28 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.neighborCut 14 .leaf .leaf))))))) (.sourceCut 32 (.neighborCut 28 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 14 (.sourceCut 16 .leaf .leaf) (.neighborCut 15 .leaf (.neighborCut 28 .leaf (.sourceCut 16 (.neighborCut 14 .leaf .leaf) .leaf))))) (.sourceCut 32 (.neighborCut 57 .leaf (.neighborCut 28 .leaf .leaf)) (.neighborCut 28 (.sourceCut 16 .leaf (.neighborCut 14 .leaf (.sourceCut 8 .leaf .leaf))) (.neighborCut 14 .leaf (.neighborCut 15 .leaf (.neighborCut 28 .leaf (.sourceCut 16 .leaf (.neighborCut 14 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,128,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context2550_header,context2703_header,context2714_header,context2725_header,context2736_header,context2747_header,context2758_header,context2769_header,context2780_header,context2791_header,context2675_header,context2686_header,context2695_header,context2696_header,context2697_header,context2698_header,context2699_header,context2700_header,context2701_header,context2702_header,context2704_header,context2705_header,context2706_header,context2707_header,context2708_header,context2709_header,context2710_header,context2711_header,context2712_header,context2713_header,context2715_header,context2716_header,context2717_header,context2718_header,context2719_header,context2720_header,context2721_header,context2722_header,context2723_header,context2724_header,context2726_header,context2727_header,context2728_header,context2729_header,context2730_header,context2731_header,context2732_header,context2733_header,context2734_header,context2735_header,context2737_header,context2738_header,context2739_header,context2740_header,context2741_header,context2742_header,context2743_header,context2744_header,context2745_header,context2746_header,context2748_header,context2749_header,context2750_header,context2751_header,context2752_header,context2753_header,context2754_header,context2755_header,context2756_header,context2757_header,context2759_header,context2760_header,context2761_header,context2762_header,context2763_header,context2764_header,context2765_header,context2766_header,context2767_header,context2768_header,context2770_header,context2771_header,context2772_header,context2773_header,context2774_header,context2775_header,context2776_header,context2777_header,context2778_header,context2779_header,context2781_header,context2782_header,context2783_header,context2784_header,context2785_header,context2786_header,context2787_header,context2788_header,context2789_header,context2790_header,context2665_header,context2666_header,context2667_header,context2668_header,context2669_header,context2670_header,context2671_header,context2672_header,context2673_header,context2674_header,context2676_header,context2677_header,context2678_header,context2679_header,context2680_header,context2681_header,context2682_header,context2683_header,context2684_header,context2685_header,context2687_header,context2688_header,context2689_header,context2690_header,context2691_header,context2692_header,context2693_header,context2694_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2745,some (fanBlockRows 986)),(2746,some (fanBlockRows 1025)),(2747,some (fanBlockRows 1036)),(2748,some (fanBlockRows 1043)),(2749,some (fanBlockRows 1044)),(2750,some (fanBlockRows 1045)),(2751,some (fanBlockRows 1046)),(2752,some (fanBlockRows 1057)),(2753,some (fanBlockRows 1068)),(2754,some (fanBlockRows 1079)),(2755,some (fanBlockRows 997)),(2756,some (fanBlockRows 1008)),(2757,some (fanBlockRows 1017)),(2758,some (fanBlockRows 1018)),(2759,some (fanBlockRows 1019)),(2760,some (fanBlockRows 1020)),(2761,some (fanBlockRows 1021)),(2762,some (fanBlockRows 1022)),(2763,some (fanBlockRows 1023)),(2764,some (fanBlockRows 1024)),(2765,some (fanBlockRows 1026)),(2766,some (fanBlockRows 1027)),(2767,some (fanBlockRows 1028)),(2768,some (fanBlockRows 1029)),(2769,some (fanBlockRows 1030)),(2770,some (fanBlockRows 1031)),(2771,some (fanBlockRows 1032)),(2772,some (fanBlockRows 1033)),(2773,some (fanBlockRows 1034)),(2774,some (fanBlockRows 1035)),(2775,some (fanBlockRows 1037)),(2776,some (fanBlockRows 1038)),(2777,some (fanBlockRows 1039)),(2778,some (fanBlockRows 1040)),(2779,some (fanBlockRows 1041)),(2780,some (fanBlockRows 1042)),(2781,some (fanBlockRows 59)),(2782,some (fanBlockRows 59)),(2783,some (fanBlockRows 59)),(2784,some (fanBlockRows 59)),(2785,some (fanBlockRows 59)),(2786,some (fanBlockRows 59)),(2787,some (fanBlockRows 59)),(2788,some (fanBlockRows 59)),(2789,some (fanBlockRows 59)),(2790,some (fanBlockRows 59)),(2791,some (fanBlockRows 59)),(2792,some (fanBlockRows 59)),(2793,some (fanBlockRows 59)),(2794,some (fanBlockRows 59)),(2795,some (fanBlockRows 59)),(2796,some (fanBlockRows 59)),(2797,some (fanBlockRows 59)),(2798,some (fanBlockRows 59)),(2799,some (fanBlockRows 59)),(2800,some (fanBlockRows 59)),(2801,some (fanBlockRows 59)),(2802,some (fanBlockRows 59)),(2803,some (fanBlockRows 59)),(2804,some (fanBlockRows 59)),(2805,some (fanBlockRows 59)),(2806,some (fanBlockRows 59)),(2807,some (fanBlockRows 59)),(2808,some (fanBlockRows 59)),(2809,some (fanBlockRows 59)),(2810,some (fanBlockRows 59)),(2811,some (fanBlockRows 59)),(2812,some (fanBlockRows 59)),(2813,some (fanBlockRows 59)),(2814,some (fanBlockRows 59)),(2815,some (fanBlockRows 1047)),(2816,some (fanBlockRows 1048)),(2817,some (fanBlockRows 1049)),(2818,some (fanBlockRows 1050)),(2819,some (fanBlockRows 1051)),(2820,some (fanBlockRows 1052)),(2821,some (fanBlockRows 1053)),(2822,some (fanBlockRows 1054)),(2823,some (fanBlockRows 1055)),(2824,some (fanBlockRows 1056)),(2825,some (fanBlockRows 1058)),(2826,some (fanBlockRows 1059)),(2827,some (fanBlockRows 1060)),(2828,some (fanBlockRows 1061)),(2829,some (fanBlockRows 1062)),(2830,some (fanBlockRows 1063)),(2831,some (fanBlockRows 1064)),(2832,some (fanBlockRows 1065)),(2833,some (fanBlockRows 1066)),(2834,some (fanBlockRows 1067)),(2835,some (fanBlockRows 1069)),(2836,some (fanBlockRows 1070)),(2837,some (fanBlockRows 1071)),(2838,some (fanBlockRows 1072)),(2839,some (fanBlockRows 1073)),(2840,some (fanBlockRows 1074)),(2841,some (fanBlockRows 1075)),(2842,some (fanBlockRows 1076)),(2843,some (fanBlockRows 1077)),(2844,some (fanBlockRows 1078)),(2845,some (fanBlockRows 987)),(2846,some (fanBlockRows 988)),(2847,some (fanBlockRows 989)),(2848,some (fanBlockRows 990)),(2849,some (fanBlockRows 991)),(2850,some (fanBlockRows 992)),(2851,some (fanBlockRows 993)),(2852,some (fanBlockRows 994)),(2853,some (fanBlockRows 995)),(2854,some (fanBlockRows 996)),(2855,some (fanBlockRows 998)),(2856,some (fanBlockRows 999)),(2857,some (fanBlockRows 1000)),(2858,some (fanBlockRows 1001)),(2859,some (fanBlockRows 1002)),(2860,some (fanBlockRows 1003)),(2861,some (fanBlockRows 1004)),(2862,some (fanBlockRows 1005)),(2863,some (fanBlockRows 1006)),(2864,some (fanBlockRows 1007)),(2865,some (fanBlockRows 1009)),(2866,some (fanBlockRows 1010)),(2867,some (fanBlockRows 1011)),(2868,some (fanBlockRows 1012)),(2869,some (fanBlockRows 1013)),(2870,some (fanBlockRows 1014)),(2871,some (fanBlockRows 1015)),(2872,some (fanBlockRows 1016))]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step03.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain11_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step03.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step03.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain11_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain11_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step03

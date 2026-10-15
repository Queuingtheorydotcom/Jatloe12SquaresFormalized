import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step13
import Compact.HistoricalCommon.C973.Step13Groups00
import Compact.HistoricalCommon.C973.Step13Groups01
import Compact.HistoricalCommon.C973.Step13Groups02
import Compact.HistoricalCommon.C973.Step13Groups03
import Compact.HistoricalCommon.C973.Step13Groups04
import Compact.HistoricalCommon.C973.Step13Groups05
import Compact.HistoricalCommon.C973.Step13Groups06
import Compact.HistoricalCommon.C973.Step13Groups07
import Compact.HistoricalCommon.C973.Step13Groups08
import Compact.HistoricalCommon.C973.Step13Groups09

namespace N12Compact.HistoricalCommon.C973.Step13
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 11 (.sourceCut 8 (.neighborCut 5 .leaf (.sourceCut 4 .leaf .leaf)) (.sourceCut 8 .leaf (.sourceCut 8 (.neighborCut 5 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 5 .leaf .leaf)))) (.neighborCut 12 (.sourceCut 8 (.neighborCut 6 .leaf (.sourceCut 4 .leaf .leaf)) (.sourceCut 8 .leaf (.neighborCut 6 .leaf (.sourceCut 8 .leaf (.neighborCut 3 .leaf .leaf))))) .leaf)) (.sourceCut 16 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 6 .leaf (.neighborCut 12 (.sourceCut 8 (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf)) .leaf) (.neighborCut 11 .leaf (.sourceCut 8 .leaf (.neighborCut 6 .leaf (.sourceCut 4 .leaf .leaf)))))))) (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 6 .leaf (.neighborCut 12 .leaf (.neighborCut 5 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.sourceCut 8 (.neighborCut 6 .leaf .leaf) .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,64,0,46⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 46) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 46) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6743_header,context6797_header,context6808_header,context6819_header,context6830_header,context6841_header,context6846_header,context6847_header,context6848_header,context6849_header,context6790_header,context1087_header,context1089_header,context1091_header,context6791_header,context6792_header,context6793_header,context6794_header,context6795_header,context6796_header,context6798_header,context6799_header,context6800_header,context6801_header,context6802_header,context6803_header,context6804_header,context6805_header,context6806_header,context6807_header,context6809_header,context6810_header,context6811_header,context6812_header,context6813_header,context6814_header,context6815_header,context6816_header,context6817_header,context6818_header,context6820_header,context6821_header,context6822_header,context6823_header,context6824_header,context6825_header,context6826_header,context6827_header,context6828_header,context6829_header,context6831_header,context6832_header,context6833_header,context6834_header,context6835_header,context6836_header,context6837_header,context6838_header,context6839_header,context6840_header,context6842_header,context6843_header,context6844_header,context6845_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1125,some (fanBlockRows 2672)),(1126,some (fanBlockRows 2680)),(1127,some (fanBlockRows 2691)),(1128,some (fanBlockRows 2702)),(1129,some (fanBlockRows 2713)),(1130,some (fanBlockRows 2724)),(1131,some (fanBlockRows 2729)),(1132,some (fanBlockRows 2730)),(1133,some (fanBlockRows 2731)),(1134,some (fanBlockRows 2732)),(1135,some (fanBlockRows 2673)),(1136,some (fanBlockRows 59)),(1137,some (fanBlockRows 59)),(1138,some (fanBlockRows 59)),(1139,some (fanBlockRows 2674)),(1140,some (fanBlockRows 2675)),(1141,some (fanBlockRows 2676)),(1142,some (fanBlockRows 2677)),(1143,some (fanBlockRows 2678)),(1144,some (fanBlockRows 2679)),(1145,some (fanBlockRows 2681)),(1146,some (fanBlockRows 2682)),(1147,some (fanBlockRows 2683)),(1148,some (fanBlockRows 2684)),(1149,some (fanBlockRows 2685)),(1150,some (fanBlockRows 2686)),(1151,some (fanBlockRows 2687)),(1152,some (fanBlockRows 2688)),(1153,some (fanBlockRows 2689)),(1154,some (fanBlockRows 2690)),(1155,some (fanBlockRows 2692)),(1156,some (fanBlockRows 2693)),(1157,some (fanBlockRows 2694)),(1158,some (fanBlockRows 2695)),(1159,some (fanBlockRows 2696)),(1160,some (fanBlockRows 2697)),(1161,some (fanBlockRows 2698)),(1162,some (fanBlockRows 2699)),(1163,some (fanBlockRows 2700)),(1164,some (fanBlockRows 2701)),(1165,some (fanBlockRows 2703)),(1166,some (fanBlockRows 2704)),(1167,some (fanBlockRows 2705)),(1168,some (fanBlockRows 2706)),(1169,some (fanBlockRows 2707)),(1170,some (fanBlockRows 2708)),(1171,some (fanBlockRows 2709)),(1172,some (fanBlockRows 2710)),(1173,some (fanBlockRows 2711)),(1174,some (fanBlockRows 2712)),(1175,some (fanBlockRows 2714)),(1176,some (fanBlockRows 2715)),(1177,some (fanBlockRows 2716)),(1178,some (fanBlockRows 2717)),(1179,some (fanBlockRows 2718)),(1180,some (fanBlockRows 2719)),(1181,some (fanBlockRows 2720)),(1182,some (fanBlockRows 2721)),(1183,some (fanBlockRows 2722)),(1184,some (fanBlockRows 2723)),(1185,some (fanBlockRows 2725)),(1186,some (fanBlockRows 2726)),(1187,some (fanBlockRows 2727)),(1188,some (fanBlockRows 2728))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step13.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 46).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain9_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step13.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step13.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain9_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain9_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step13

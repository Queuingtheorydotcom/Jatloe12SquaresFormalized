import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step21
import Compact.HistoricalCommon.C973.Step21Groups00
import Compact.HistoricalCommon.C973.Step21Groups01
import Compact.HistoricalCommon.C973.Step21Groups02
import Compact.HistoricalCommon.C973.Step21Groups03
import Compact.HistoricalCommon.C973.Step21Groups04
import Compact.HistoricalCommon.C973.Step21Groups05
import Compact.HistoricalCommon.C973.Step21Groups06
import Compact.HistoricalCommon.C973.Step21Groups07
import Compact.HistoricalCommon.C973.Step21Groups08
import Compact.HistoricalCommon.C973.Step21Groups09
import Compact.HistoricalCommon.C973.Step21Groups10
import Compact.HistoricalCommon.C973.Step21Groups11

namespace N12Compact.HistoricalCommon.C973.Step21
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44,group45,group46]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope,group45_scope,group46_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 31 (.neighborCut 27 (.sourceCut 15 (.neighborCut 6 (.sourceCut 7 .leaf .leaf) (.neighborCut 3 (.sourceCut 7 .leaf .leaf) (.neighborCut 4 (.sourceCut 7 .leaf .leaf) (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf))))) (.sourceCut 8 (.neighborCut 13 .leaf (.neighborCut 7 .leaf .leaf)) .leaf)) .leaf) (.sourceCut 16 (.neighborCut 27 (.sourceCut 8 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 7 .leaf (.neighborCut 3 .leaf .leaf)))))) (.neighborCut 13 (.sourceCut 8 .leaf (.neighborCut 6 .leaf (.sourceCut 4 .leaf .leaf))) .leaf)) (.sourceCut 8 (.neighborCut 13 .leaf (.neighborCut 7 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 7 .leaf (.sourceCut 4 .leaf .leaf))))))))) (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 13 .leaf (.neighborCut 7 .leaf (.sourceCut 4 .leaf .leaf)))))))))))))

theorem partition_checked : partition.Check ⟨0,63,0,54⟩ scopes := by decide +kernel

theorem covered (i : Fin 63) (j : Fin 54) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 63) (j : Fin 54) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7592_header,context7660_header,context7671_header,context7682_header,context7693_header,context7704_header,context7708_header,context7709_header,context7710_header,context7711_header,context7650_header,context7651_header,context7652_header,context7653_header,context7654_header,context7655_header,context7656_header,context7657_header,context7658_header,context7659_header,context7661_header,context7662_header,context7663_header,context7664_header,context7665_header,context7666_header,context7667_header,context7668_header,context7669_header,context7670_header,context7672_header,context7673_header,context7674_header,context7675_header,context7676_header,context7677_header,context7678_header,context7679_header,context7680_header,context7681_header,context7683_header,context7684_header,context7685_header,context7686_header,context7687_header,context7688_header,context7689_header,context7690_header,context7691_header,context7692_header,context7694_header,context7695_header,context7696_header,context7697_header,context7698_header,context7699_header,context7700_header,context7701_header,context7702_header,context7703_header,context7705_header,context7706_header,context7707_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 63).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6787,some (fanBlockRows 3083)),(6788,some (fanBlockRows 3092)),(6789,some (fanBlockRows 3094)),(6790,some (fanBlockRows 3096)),(6791,some (fanBlockRows 3107)),(6792,some (fanBlockRows 3118)),(6793,some (fanBlockRows 3122)),(6794,some (fanBlockRows 3123)),(6795,some (fanBlockRows 3124)),(6796,some (fanBlockRows 3125)),(6797,some (fanBlockRows 3084)),(6798,some (fanBlockRows 3085)),(6799,some (fanBlockRows 3086)),(6800,some (fanBlockRows 3087)),(6801,some (fanBlockRows 3088)),(6802,some (fanBlockRows 3089)),(6803,some (fanBlockRows 3090)),(6804,some (fanBlockRows 3091)),(6805,some (fanBlockRows 59)),(6806,some (fanBlockRows 59)),(6807,some (fanBlockRows 3093)),(6808,some (fanBlockRows 59)),(6809,some (fanBlockRows 59)),(6810,some (fanBlockRows 59)),(6811,some (fanBlockRows 59)),(6812,some (fanBlockRows 59)),(6813,some (fanBlockRows 59)),(6814,some (fanBlockRows 59)),(6815,some (fanBlockRows 59)),(6816,some (fanBlockRows 59)),(6817,some (fanBlockRows 59)),(6818,some (fanBlockRows 59)),(6819,some (fanBlockRows 59)),(6820,some (fanBlockRows 59)),(6821,some (fanBlockRows 59)),(6822,some (fanBlockRows 59)),(6823,some (fanBlockRows 59)),(6824,some (fanBlockRows 59)),(6825,some (fanBlockRows 59)),(6826,some (fanBlockRows 3095)),(6827,some (fanBlockRows 3097)),(6828,some (fanBlockRows 3098)),(6829,some (fanBlockRows 3099)),(6830,some (fanBlockRows 3100)),(6831,some (fanBlockRows 3101)),(6832,some (fanBlockRows 3102)),(6833,some (fanBlockRows 3103)),(6834,some (fanBlockRows 3104)),(6835,some (fanBlockRows 3105)),(6836,some (fanBlockRows 3106)),(6837,some (fanBlockRows 3108)),(6838,some (fanBlockRows 3109)),(6839,some (fanBlockRows 3110)),(6840,some (fanBlockRows 3111)),(6841,some (fanBlockRows 3112)),(6842,some (fanBlockRows 3113)),(6843,some (fanBlockRows 3114)),(6844,some (fanBlockRows 3115)),(6845,some (fanBlockRows 3116)),(6846,some (fanBlockRows 3117)),(6847,some (fanBlockRows 3119)),(6848,some (fanBlockRows 3120)),(6849,some (fanBlockRows 3121))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step21.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 54).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain8_16Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step21.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step21.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain8_16Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain8_16Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step21

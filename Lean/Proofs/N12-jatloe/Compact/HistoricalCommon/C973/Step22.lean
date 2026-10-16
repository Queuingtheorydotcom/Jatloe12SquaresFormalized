import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step22
import Compact.HistoricalCommon.C973.Step22Groups00
import Compact.HistoricalCommon.C973.Step22Groups01
import Compact.HistoricalCommon.C973.Step22Groups02
import Compact.HistoricalCommon.C973.Step22Groups03
import Compact.HistoricalCommon.C973.Step22Groups04
import Compact.HistoricalCommon.C973.Step22Groups05
import Compact.HistoricalCommon.C973.Step22Groups06
import Compact.HistoricalCommon.C973.Step22Groups07
import Compact.HistoricalCommon.C973.Step22Groups08
import Compact.HistoricalCommon.C973.Step22Groups09

namespace N12Compact.HistoricalCommon.C973.Step22
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 15 (.neighborCut 10 (.sourceCut 7 (.neighborCut 5 .leaf (.neighborCut 2 .leaf .leaf)) .leaf) (.neighborCut 5 (.sourceCut 7 .leaf .leaf) (.neighborCut 6 .leaf (.neighborCut 11 (.sourceCut 7 .leaf (.sourceCut 4 .leaf (.neighborCut 5 .leaf .leaf))) .leaf)))) (.sourceCut 15 (.neighborCut 10 .leaf (.neighborCut 5 (.sourceCut 7 .leaf .leaf) (.neighborCut 6 (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf)) .leaf))) (.neighborCut 10 (.sourceCut 7 .leaf (.sourceCut 8 (.neighborCut 5 .leaf (.neighborCut 2 .leaf .leaf)) (.sourceCut 8 (.neighborCut 5 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 5 .leaf .leaf)))) (.neighborCut 11 .leaf (.sourceCut 15 .leaf (.sourceCut 8 (.neighborCut 5 .leaf (.neighborCut 6 .leaf .leaf)) (.neighborCut 11 .leaf (.neighborCut 5 (.sourceCut 4 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,61,0,43⟩ scopes := by decide +kernel

theorem covered (i : Fin 61) (j : Fin 43) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 61) (j : Fin 43) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7765_header,context7776_header,context7787_header,context7798_header,context7809_header,context7812_header,context7813_header,context7814_header,context7815_header,context7712_header,context7756_header,context7757_header,context7758_header,context7759_header,context7760_header,context7761_header,context7762_header,context7763_header,context7764_header,context7766_header,context7767_header,context7768_header,context7769_header,context7770_header,context7771_header,context7772_header,context7773_header,context7774_header,context7775_header,context7777_header,context7778_header,context7779_header,context7780_header,context7781_header,context7782_header,context7783_header,context7784_header,context7785_header,context7786_header,context7788_header,context7789_header,context7790_header,context7791_header,context7792_header,context7793_header,context7794_header,context7795_header,context7796_header,context7797_header,context7799_header,context7800_header,context7801_header,context7802_header,context7803_header,context7804_header,context7805_header,context7806_header,context7807_header,context7808_header,context7810_header,context7811_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 61).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6893,none),(6894,some (fanBlockRows 3136)),(6895,some (fanBlockRows 3147)),(6896,some (fanBlockRows 3158)),(6897,some (fanBlockRows 3169)),(6898,some (fanBlockRows 3180)),(6899,some (fanBlockRows 3183)),(6900,some (fanBlockRows 3184)),(6901,some (fanBlockRows 3185)),(6902,some (fanBlockRows 3186)),(6903,some (fanBlockRows 3126)),(6904,some (fanBlockRows 3127)),(6905,some (fanBlockRows 3128)),(6906,some (fanBlockRows 3129)),(6907,some (fanBlockRows 3130)),(6908,some (fanBlockRows 3131)),(6909,some (fanBlockRows 3132)),(6910,some (fanBlockRows 3133)),(6911,some (fanBlockRows 3134)),(6912,some (fanBlockRows 3135)),(6913,some (fanBlockRows 3137)),(6914,some (fanBlockRows 3138)),(6915,some (fanBlockRows 3139)),(6916,some (fanBlockRows 3140)),(6917,some (fanBlockRows 3141)),(6918,some (fanBlockRows 3142)),(6919,some (fanBlockRows 3143)),(6920,some (fanBlockRows 3144)),(6921,some (fanBlockRows 3145)),(6922,some (fanBlockRows 3146)),(6923,some (fanBlockRows 3148)),(6924,some (fanBlockRows 3149)),(6925,some (fanBlockRows 3150)),(6926,some (fanBlockRows 3151)),(6927,some (fanBlockRows 3152)),(6928,some (fanBlockRows 3153)),(6929,some (fanBlockRows 3154)),(6930,some (fanBlockRows 3155)),(6931,some (fanBlockRows 3156)),(6932,some (fanBlockRows 3157)),(6933,some (fanBlockRows 3159)),(6934,some (fanBlockRows 3160)),(6935,some (fanBlockRows 3161)),(6936,some (fanBlockRows 3162)),(6937,some (fanBlockRows 3163)),(6938,some (fanBlockRows 3164)),(6939,some (fanBlockRows 3165)),(6940,some (fanBlockRows 3166)),(6941,some (fanBlockRows 3167)),(6942,some (fanBlockRows 3168)),(6943,some (fanBlockRows 3170)),(6944,some (fanBlockRows 3171)),(6945,some (fanBlockRows 3172)),(6946,some (fanBlockRows 3173)),(6947,some (fanBlockRows 3174)),(6948,some (fanBlockRows 3175)),(6949,some (fanBlockRows 3176)),(6950,some (fanBlockRows 3177)),(6951,some (fanBlockRows 3178)),(6952,some (fanBlockRows 3179)),(6953,some (fanBlockRows 3181)),(6954,some (fanBlockRows 3182)),(6955,none),(6956,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step22.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 43).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain5_22Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step22.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step22.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain5_22Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain5_22Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step22

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step24
import Compact.HistoricalCommon.C973.Step24Groups00
import Compact.HistoricalCommon.C973.Step24Groups01
import Compact.HistoricalCommon.C973.Step24Groups02
import Compact.HistoricalCommon.C973.Step24Groups03
import Compact.HistoricalCommon.C973.Step24Groups04
import Compact.HistoricalCommon.C973.Step24Groups05
import Compact.HistoricalCommon.C973.Step24Groups06

namespace N12Compact.HistoricalCommon.C973.Step24
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 7 (.neighborCut 4 .leaf .leaf) (.sourceCut 14 (.neighborCut 4 .leaf .leaf) (.sourceCut 13 (.neighborCut 4 .leaf .leaf) .leaf)))) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 7 .leaf (.sourceCut 14 (.neighborCut 8 .leaf (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf))) (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 2 .leaf .leaf))) (.neighborCut 8 (.sourceCut 7 .leaf .leaf) .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,54,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 54) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 54) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7925_header,context8000_header,context8008_header,context8019_header,context8030_header,context8035_header,context8036_header,context8037_header,context8038_header,context8039_header,context7990_header,context7991_header,context7992_header,context7993_header,context7994_header,context7995_header,context7996_header,context7997_header,context7998_header,context7999_header,context8001_header,context7615_header,context7617_header,context7619_header,context8002_header,context8003_header,context8004_header,context8005_header,context8006_header,context8007_header,context8009_header,context8010_header,context8011_header,context8012_header,context8013_header,context8014_header,context8015_header,context8016_header,context8017_header,context8018_header,context8020_header,context8021_header,context8022_header,context8023_header,context8024_header,context8025_header,context8026_header,context8027_header,context8028_header,context8029_header,context8031_header,context8032_header,context8033_header,context8034_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 54).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7532,some (fanBlockRows 3196)),(7533,some (fanBlockRows 3207)),(7534,some (fanBlockRows 3215)),(7535,some (fanBlockRows 3226)),(7536,some (fanBlockRows 3237)),(7537,some (fanBlockRows 3242)),(7538,some (fanBlockRows 3243)),(7539,some (fanBlockRows 3244)),(7540,some (fanBlockRows 3245)),(7541,some (fanBlockRows 3246)),(7542,some (fanBlockRows 3197)),(7543,some (fanBlockRows 3198)),(7544,some (fanBlockRows 3199)),(7545,some (fanBlockRows 3200)),(7546,some (fanBlockRows 3201)),(7547,some (fanBlockRows 3202)),(7548,some (fanBlockRows 3203)),(7549,some (fanBlockRows 3204)),(7550,some (fanBlockRows 3205)),(7551,some (fanBlockRows 3206)),(7552,some (fanBlockRows 3208)),(7553,some (fanBlockRows 59)),(7554,some (fanBlockRows 59)),(7555,some (fanBlockRows 59)),(7556,some (fanBlockRows 3209)),(7557,some (fanBlockRows 3210)),(7558,some (fanBlockRows 3211)),(7559,some (fanBlockRows 3212)),(7560,some (fanBlockRows 3213)),(7561,some (fanBlockRows 3214)),(7562,some (fanBlockRows 3216)),(7563,some (fanBlockRows 3217)),(7564,some (fanBlockRows 3218)),(7565,some (fanBlockRows 3219)),(7566,some (fanBlockRows 3220)),(7567,some (fanBlockRows 3221)),(7568,some (fanBlockRows 3222)),(7569,some (fanBlockRows 3223)),(7570,some (fanBlockRows 3224)),(7571,some (fanBlockRows 3225)),(7572,some (fanBlockRows 3227)),(7573,some (fanBlockRows 3228)),(7574,some (fanBlockRows 3229)),(7575,some (fanBlockRows 3230)),(7576,some (fanBlockRows 3231)),(7577,some (fanBlockRows 3232)),(7578,some (fanBlockRows 3233)),(7579,some (fanBlockRows 3234)),(7580,some (fanBlockRows 3235)),(7581,some (fanBlockRows 3236)),(7582,some (fanBlockRows 3238)),(7583,some (fanBlockRows 3239)),(7584,some (fanBlockRows 3240)),(7585,some (fanBlockRows 3241))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step24.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain11_18Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step24.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step24.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain11_18Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain11_18Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step24

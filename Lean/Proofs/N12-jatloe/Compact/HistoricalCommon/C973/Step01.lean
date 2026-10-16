import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step01
import Compact.HistoricalCommon.C973.Step01Groups00
import Compact.HistoricalCommon.C973.Step01Groups01
import Compact.HistoricalCommon.C973.Step01Groups02
import Compact.HistoricalCommon.C973.Step01Groups03
import Compact.HistoricalCommon.C973.Step01Groups04
import Compact.HistoricalCommon.C973.Step01Groups05
import Compact.HistoricalCommon.C973.Step01Groups06
import Compact.HistoricalCommon.C973.Step01Groups07
import Compact.HistoricalCommon.C973.Step01Groups08
import Compact.HistoricalCommon.C973.Step01Groups09
import Compact.HistoricalCommon.C973.Step01Groups10
import Compact.HistoricalCommon.C973.Step01Groups11
import Compact.HistoricalCommon.C973.Step01Groups12

namespace N12Compact.HistoricalCommon.C973.Step01
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
  (.sourceCut 24 (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 4 .leaf .leaf) (.sourceCut 6 .leaf .leaf))) (.neighborCut 8 .leaf (.sourceCut 12 (.neighborCut 16 .leaf (.sourceCut 6 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 8 (.sourceCut 3 .leaf .leaf) (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf .leaf)))))) (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 8 (.sourceCut 3 .leaf (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf))) (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))))))) (.neighborCut 8 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) (.neighborCut 8 .leaf (.sourceCut 12 (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 6 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 (.sourceCut 6 .leaf (.neighborCut 4 .leaf .leaf)) .leaf)))) (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.sourceCut 6 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,49,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 49) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 49) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7361_header,context7435_header,context7436_header,context7443_header,context7454_header,context7465_header,context7470_header,context7471_header,context7472_header,context7473_header,context7426_header,context7427_header,context7428_header,context7429_header,context7430_header,context7431_header,context7432_header,context7433_header,context7434_header,context7437_header,context7438_header,context7439_header,context7440_header,context7441_header,context7442_header,context7444_header,context7445_header,context7446_header,context7447_header,context7448_header,context7449_header,context7450_header,context7451_header,context7452_header,context7453_header,context7455_header,context7456_header,context7457_header,context7458_header,context7459_header,context7460_header,context7461_header,context7462_header,context7463_header,context7464_header,context7466_header,context7467_header,context7468_header,context7469_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 49).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7414,some (fanBlockRows 2982)),(7415,some (fanBlockRows 2992)),(7416,some (fanBlockRows 2993)),(7417,some (fanBlockRows 3000)),(7418,some (fanBlockRows 3011)),(7419,some (fanBlockRows 3022)),(7420,some (fanBlockRows 3027)),(7421,some (fanBlockRows 3028)),(7422,some (fanBlockRows 3029)),(7423,some (fanBlockRows 3030)),(7424,some (fanBlockRows 2983)),(7425,some (fanBlockRows 2984)),(7426,some (fanBlockRows 2985)),(7427,some (fanBlockRows 2986)),(7428,some (fanBlockRows 2987)),(7429,some (fanBlockRows 2988)),(7430,some (fanBlockRows 2989)),(7431,some (fanBlockRows 2990)),(7432,some (fanBlockRows 2991)),(7433,none),(7434,none),(7435,none),(7436,none),(7437,none),(7438,none),(7439,none),(7440,none),(7441,none),(7442,none),(7443,none),(7444,none),(7445,none),(7446,none),(7447,none),(7448,some (fanBlockRows 2994)),(7449,some (fanBlockRows 2995)),(7450,some (fanBlockRows 2996)),(7451,some (fanBlockRows 2997)),(7452,some (fanBlockRows 2998)),(7453,some (fanBlockRows 2999)),(7454,some (fanBlockRows 3001)),(7455,some (fanBlockRows 3002)),(7456,some (fanBlockRows 3003)),(7457,some (fanBlockRows 3004)),(7458,some (fanBlockRows 3005)),(7459,some (fanBlockRows 3006)),(7460,some (fanBlockRows 3007)),(7461,some (fanBlockRows 3008)),(7462,some (fanBlockRows 3009)),(7463,some (fanBlockRows 3010)),(7464,some (fanBlockRows 3012)),(7465,some (fanBlockRows 3013)),(7466,some (fanBlockRows 3014)),(7467,some (fanBlockRows 3015)),(7468,some (fanBlockRows 3016)),(7469,some (fanBlockRows 3017)),(7470,some (fanBlockRows 3018)),(7471,some (fanBlockRows 3019)),(7472,some (fanBlockRows 3020)),(7473,some (fanBlockRows 3021)),(7474,some (fanBlockRows 3023)),(7475,some (fanBlockRows 3024)),(7476,some (fanBlockRows 3025)),(7477,some (fanBlockRows 3026))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step01.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain11_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step01.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step01.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain11_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain11_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step01

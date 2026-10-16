import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C978.DirectPruning.Step00
import Compact.HistoricalCommon.C978.Step00Groups00
import Compact.HistoricalCommon.C978.Step00Groups01
import Compact.HistoricalCommon.C978.Step00Groups02
import Compact.HistoricalCommon.C978.Step00Groups03
import Compact.HistoricalCommon.C978.Step00Groups04
import Compact.HistoricalCommon.C978.Step00Groups05
import Compact.HistoricalCommon.C978.Step00Groups06
import Compact.HistoricalCommon.C978.Step00Groups07
import Compact.HistoricalCommon.C978.Step00Groups08
import Compact.HistoricalCommon.C978.Step00Groups09

namespace N12Compact.HistoricalCommon.C978.Step00
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
  (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.sourceCut 6 .leaf (.sourceCut 3 .leaf .leaf))))))) (.sourceCut 13 (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 4 (.sourceCut 6 .leaf .leaf) .leaf)))))) (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 16 (.sourceCut 6 (.neighborCut 8 .leaf .leaf) .leaf) (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 .leaf .leaf))))) (.neighborCut 8 (.sourceCut 7 .leaf .leaf) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 7 .leaf .leaf) (.neighborCut 8 .leaf (.sourceCut 7 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,53,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 53) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 53) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8883_header,context8894_header,context8901_header,context8902_header,context8903_header,context8904_header,context8905_header,context8845_header,context8854_header,context8855_header,context8856_header,context8857_header,context8858_header,context8859_header,context8860_header,context8861_header,context8862_header,context8863_header,context8864_header,context8865_header,context8866_header,context8867_header,context8868_header,context8869_header,context8870_header,context8871_header,context8872_header,context8873_header,context8874_header,context8875_header,context8876_header,context8877_header,context8878_header,context8879_header,context8880_header,context8881_header,context8882_header,context8884_header,context8885_header,context8886_header,context8887_header,context8888_header,context8889_header,context8890_header,context8891_header,context8892_header,context8893_header,context8895_header,context8896_header,context8897_header,context8898_header,context8899_header,context8900_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 53).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(8441,none),(8442,none),(8443,none),(8444,some (fanBlockRows 3748)),(7354,some (fanBlockRows 3759)),(7355,some (fanBlockRows 3766)),(7356,some (fanBlockRows 3767)),(7357,some (fanBlockRows 3768)),(7358,some (fanBlockRows 3769)),(7359,some (fanBlockRows 3770)),(7360,some (fanBlockRows 3718)),(7361,some (fanBlockRows 3719)),(7362,some (fanBlockRows 3720)),(7363,some (fanBlockRows 3721)),(7364,some (fanBlockRows 3722)),(7365,some (fanBlockRows 3723)),(7366,some (fanBlockRows 3724)),(7367,some (fanBlockRows 3725)),(7368,some (fanBlockRows 3726)),(7369,some (fanBlockRows 3727)),(7370,some (fanBlockRows 3728)),(7371,some (fanBlockRows 3729)),(7372,some (fanBlockRows 3730)),(7373,some (fanBlockRows 3731)),(7374,some (fanBlockRows 3732)),(7375,some (fanBlockRows 3733)),(7376,some (fanBlockRows 3734)),(7377,some (fanBlockRows 3735)),(7378,some (fanBlockRows 3736)),(7379,some (fanBlockRows 3737)),(7380,some (fanBlockRows 3738)),(7381,some (fanBlockRows 3739)),(7382,some (fanBlockRows 3740)),(7383,some (fanBlockRows 3741)),(7384,some (fanBlockRows 3742)),(7385,some (fanBlockRows 3743)),(7386,some (fanBlockRows 3744)),(7387,some (fanBlockRows 3745)),(7388,some (fanBlockRows 3746)),(7389,some (fanBlockRows 3747)),(7390,some (fanBlockRows 3749)),(7391,some (fanBlockRows 3750)),(7392,some (fanBlockRows 3751)),(7393,some (fanBlockRows 3752)),(7394,some (fanBlockRows 3753)),(7395,some (fanBlockRows 3754)),(8445,some (fanBlockRows 3755)),(8446,some (fanBlockRows 3756)),(8447,some (fanBlockRows 3757)),(8448,some (fanBlockRows 3758)),(8449,some (fanBlockRows 3760)),(8450,some (fanBlockRows 3761)),(8451,some (fanBlockRows 3762)),(8452,some (fanBlockRows 3763)),(8453,some (fanBlockRows 3764)),(8454,some (fanBlockRows 3765)),(8455,none),(8456,none),(8457,none),(8458,none),(8459,none),(8460,none),(8461,none),(8462,none)]

theorem planHeaders_exact :
    N12Compact.C978DirectPruning.Step00.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C978.continuousScout978Domain5_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C978DirectPruning.Step00.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C978DirectPruning.Step00.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C978.continuousScout978Domain5_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C978.continuousScout978Domain5_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C978.Step00

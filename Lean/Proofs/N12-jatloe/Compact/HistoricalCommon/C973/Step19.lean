import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step19
import Compact.HistoricalCommon.C973.Step19Groups00
import Compact.HistoricalCommon.C973.Step19Groups01
import Compact.HistoricalCommon.C973.Step19Groups02
import Compact.HistoricalCommon.C973.Step19Groups03
import Compact.HistoricalCommon.C973.Step19Groups04
import Compact.HistoricalCommon.C973.Step19Groups05
import Compact.HistoricalCommon.C973.Step19Groups06
import Compact.HistoricalCommon.C973.Step19Groups07
import Compact.HistoricalCommon.C973.Step19Groups08
import Compact.HistoricalCommon.C973.Step19Groups09
import Compact.HistoricalCommon.C973.Step19Groups10
import Compact.HistoricalCommon.C973.Step19Groups11

namespace N12Compact.HistoricalCommon.C973.Step19
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 24 (.neighborCut 7 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.neighborCut 3 .leaf .leaf)))) (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 4 .leaf .leaf) (.neighborCut 4 .leaf (.neighborCut 2 .leaf .leaf)))) (.neighborCut 7 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.neighborCut 4 .leaf .leaf))) (.neighborCut 7 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.neighborCut 3 .leaf .leaf)))) (.neighborCut 8 .leaf .leaf)))))) (.neighborCut 15 (.sourceCut 12 (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.sourceCut 6 .leaf .leaf))) .leaf) (.neighborCut 7 (.sourceCut 12 .leaf .leaf) (.neighborCut 4 (.sourceCut 12 .leaf .leaf) (.neighborCut 4 (.sourceCut 12 .leaf .leaf) (.neighborCut 7 (.sourceCut 12 (.neighborCut 3 .leaf .leaf) .leaf) (.neighborCut 8 .leaf (.sourceCut 12 .leaf (.sourceCut 6 .leaf (.sourceCut 3 .leaf (.neighborCut 7 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,48,0,60⟩ scopes := by decide +kernel

theorem covered (i : Fin 48) (j : Fin 60) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 48) (j : Fin 60) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7257_header,context7315_header,context7326_header,context7335_header,context7346_header,context7314_header,context7316_header,context7317_header,context7318_header,context7319_header,context7320_header,context7321_header,context7322_header,context7323_header,context7324_header,context7325_header,context7327_header,context7328_header,context7329_header,context7330_header,context7331_header,context7332_header,context7333_header,context7334_header,context7336_header,context7337_header,context7338_header,context7339_header,context7340_header,context7341_header,context7342_header,context7343_header,context7344_header,context7345_header,context7347_header,context7348_header,context7349_header,context7350_header,context7351_header,context7352_header,context7353_header,context7354_header,context7355_header,context7356_header,context7357_header,context7358_header,context7359_header,context7360_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 48).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(513,some (fanBlockRows 2934)),(514,some (fanBlockRows 2936)),(515,some (fanBlockRows 2947)),(516,some (fanBlockRows 2956)),(517,some (fanBlockRows 2967)),(518,none),(519,none),(520,none),(521,none),(522,none),(523,none),(524,none),(525,none),(526,none),(527,none),(528,none),(529,none),(530,none),(531,none),(532,some (fanBlockRows 2935)),(533,some (fanBlockRows 2937)),(534,some (fanBlockRows 2938)),(535,some (fanBlockRows 2939)),(536,some (fanBlockRows 2940)),(537,some (fanBlockRows 2941)),(538,some (fanBlockRows 2942)),(539,some (fanBlockRows 2943)),(540,some (fanBlockRows 2944)),(541,some (fanBlockRows 2945)),(542,some (fanBlockRows 2946)),(543,some (fanBlockRows 2948)),(544,some (fanBlockRows 2949)),(545,none),(546,none),(547,some (fanBlockRows 2950)),(548,some (fanBlockRows 2951)),(549,some (fanBlockRows 2952)),(550,some (fanBlockRows 2953)),(551,some (fanBlockRows 2954)),(552,some (fanBlockRows 2955)),(553,some (fanBlockRows 2957)),(554,some (fanBlockRows 2958)),(555,some (fanBlockRows 2959)),(556,some (fanBlockRows 2960)),(557,some (fanBlockRows 2961)),(558,some (fanBlockRows 2962)),(559,some (fanBlockRows 2963)),(560,some (fanBlockRows 2964)),(561,some (fanBlockRows 2965)),(562,some (fanBlockRows 2966)),(563,some (fanBlockRows 2968)),(564,some (fanBlockRows 2969)),(565,some (fanBlockRows 2970)),(566,some (fanBlockRows 2971)),(567,some (fanBlockRows 2972)),(568,some (fanBlockRows 2973)),(569,some (fanBlockRows 2974)),(570,some (fanBlockRows 2975)),(571,some (fanBlockRows 2976)),(572,some (fanBlockRows 2977)),(573,some (fanBlockRows 2978)),(574,some (fanBlockRows 2979)),(575,some (fanBlockRows 2980)),(576,some (fanBlockRows 2981))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step19.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 60).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain0_19Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step19.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step19.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain0_19Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain0_19Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step19

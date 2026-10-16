import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step17
import Compact.HistoricalCommon.C973.Step17Groups00
import Compact.HistoricalCommon.C973.Step17Groups01
import Compact.HistoricalCommon.C973.Step17Groups02
import Compact.HistoricalCommon.C973.Step17Groups03
import Compact.HistoricalCommon.C973.Step17Groups04
import Compact.HistoricalCommon.C973.Step17Groups05
import Compact.HistoricalCommon.C973.Step17Groups06
import Compact.HistoricalCommon.C973.Step17Groups07
import Compact.HistoricalCommon.C973.Step17Groups08

namespace N12Compact.HistoricalCommon.C973.Step17
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 8 (.sourceCut 14 .leaf (.sourceCut 14 .leaf (.sourceCut 14 .leaf (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf))))) (.neighborCut 8 (.sourceCut 7 .leaf (.sourceCut 7 (.neighborCut 4 .leaf .leaf) (.sourceCut 7 .leaf (.sourceCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 7 .leaf (.sourceCut 7 (.neighborCut 4 .leaf .leaf) .leaf))))))) (.neighborCut 16 .leaf (.sourceCut 14 (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf)) .leaf)) (.sourceCut 14 (.neighborCut 8 (.sourceCut 7 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 8 .leaf .leaf)) (.sourceCut 14 (.neighborCut 8 (.sourceCut 7 .leaf .leaf) (.neighborCut 8 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 7 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,57,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 57) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 57) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7142_header,context7143_header,context7144_header,context7145_header,context7025_header,context7090_header,context7091_header,context7092_header,context7093_header,context7094_header,context7095_header,context7096_header,context7097_header,context7098_header,context7099_header,context7100_header,context7101_header,context7102_header,context7103_header,context7104_header,context7105_header,context7106_header,context7107_header,context7108_header,context7109_header,context7110_header,context7111_header,context7112_header,context7113_header,context7114_header,context7115_header,context7116_header,context7117_header,context7118_header,context7119_header,context7120_header,context7121_header,context7122_header,context7123_header,context7124_header,context7125_header,context7126_header,context7127_header,context7128_header,context7129_header,context7130_header,context7131_header,context7132_header,context7133_header,context7134_header,context7135_header,context7136_header,context7137_header,context7138_header,context7139_header,context7140_header,context7141_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 57).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6250,none),(6251,none),(6252,none),(6253,none),(6254,none),(6255,none),(6256,some (fanBlockRows 2886)),(6257,some (fanBlockRows 2887)),(6258,some (fanBlockRows 2888)),(6259,some (fanBlockRows 2889)),(6260,some (fanBlockRows 2833)),(6261,some (fanBlockRows 2834)),(6262,some (fanBlockRows 2835)),(6263,some (fanBlockRows 2836)),(6264,some (fanBlockRows 2837)),(6265,some (fanBlockRows 2838)),(6266,some (fanBlockRows 2839)),(6267,some (fanBlockRows 2840)),(6268,some (fanBlockRows 2841)),(6269,some (fanBlockRows 2842)),(6270,some (fanBlockRows 2843)),(6271,some (fanBlockRows 2844)),(6272,some (fanBlockRows 2845)),(6273,some (fanBlockRows 2846)),(6274,some (fanBlockRows 2847)),(6275,some (fanBlockRows 2848)),(6276,some (fanBlockRows 2849)),(6277,some (fanBlockRows 2850)),(6278,some (fanBlockRows 2851)),(6279,some (fanBlockRows 2852)),(6280,some (fanBlockRows 2853)),(6281,some (fanBlockRows 2854)),(6282,some (fanBlockRows 2855)),(6283,some (fanBlockRows 2856)),(6284,some (fanBlockRows 2857)),(6285,some (fanBlockRows 2858)),(6286,some (fanBlockRows 2859)),(6287,some (fanBlockRows 2860)),(6288,some (fanBlockRows 2861)),(6289,some (fanBlockRows 2862)),(6290,some (fanBlockRows 2863)),(6291,some (fanBlockRows 2864)),(6292,some (fanBlockRows 2865)),(6293,some (fanBlockRows 2866)),(6294,some (fanBlockRows 2867)),(6295,some (fanBlockRows 2868)),(6296,some (fanBlockRows 2869)),(6297,some (fanBlockRows 2870)),(6298,some (fanBlockRows 2871)),(6299,some (fanBlockRows 2872)),(6300,some (fanBlockRows 2873)),(6301,some (fanBlockRows 2874)),(6302,some (fanBlockRows 2875)),(6303,some (fanBlockRows 2876)),(6304,some (fanBlockRows 2877)),(6305,some (fanBlockRows 2878)),(6306,some (fanBlockRows 2879)),(6307,some (fanBlockRows 2880)),(6308,some (fanBlockRows 2881)),(6309,some (fanBlockRows 2882)),(6310,some (fanBlockRows 2883)),(6311,some (fanBlockRows 2884)),(6312,some (fanBlockRows 2885)),(6313,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step17.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain3_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step17.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step17.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain3_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain3_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step17

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step18
import Compact.HistoricalCommon.C973.Step18Groups00
import Compact.HistoricalCommon.C973.Step18Groups01
import Compact.HistoricalCommon.C973.Step18Groups02
import Compact.HistoricalCommon.C973.Step18Groups03
import Compact.HistoricalCommon.C973.Step18Groups04
import Compact.HistoricalCommon.C973.Step18Groups05
import Compact.HistoricalCommon.C973.Step18Groups06
import Compact.HistoricalCommon.C973.Step18Groups07
import Compact.HistoricalCommon.C973.Step18Groups08
import Compact.HistoricalCommon.C973.Step18Groups09

namespace N12Compact.HistoricalCommon.C973.Step18
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
  (.sourceCut 12 (.neighborCut 7 .leaf (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 (.sourceCut 6 .leaf .leaf) .leaf)))))) (.sourceCut 12 (.neighborCut 7 .leaf (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 .leaf (.neighborCut 4 (.sourceCut 6 .leaf .leaf) (.neighborCut 4 .leaf (.neighborCut 16 .leaf .leaf)))))) (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.sourceCut 12 (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 6 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 (.sourceCut 6 .leaf (.neighborCut 4 .leaf .leaf)) .leaf))) (.neighborCut 16 .leaf (.sourceCut 6 (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 .leaf (.sourceCut 3 .leaf .leaf))))))))))))

theorem partition_checked : partition.Check ⟨0,48,0,63⟩ scopes := by decide +kernel

theorem covered (i : Fin 48) (j : Fin 63) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 48) (j : Fin 63) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7146_header,context7219_header,context7210_header,context7211_header,context7212_header,context7213_header,context7214_header,context7215_header,context7216_header,context7217_header,context7218_header,context7220_header,context7221_header,context7222_header,context7223_header,context7224_header,context7225_header,context7226_header,context7227_header,context7228_header,context7229_header,context7230_header,context7231_header,context7232_header,context7233_header,context7234_header,context7235_header,context7236_header,context7237_header,context7238_header,context7239_header,context7240_header,context7241_header,context7242_header,context7243_header,context7244_header,context7245_header,context7246_header,context7247_header,context7248_header,context7249_header,context7250_header,context7251_header,context7252_header,context7253_header,context7254_header,context7255_header,context7256_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 48).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(0,some (fanBlockRows 2890)),(1,some (fanBlockRows 2899)),(2,none),(3,none),(4,none),(5,none),(6,none),(7,none),(8,none),(9,none),(10,some (fanBlockRows 2891)),(11,some (fanBlockRows 2892)),(12,none),(13,some (fanBlockRows 2893)),(14,some (fanBlockRows 2894)),(15,some (fanBlockRows 2895)),(16,some (fanBlockRows 2896)),(17,some (fanBlockRows 2897)),(18,some (fanBlockRows 2898)),(19,some (fanBlockRows 59)),(20,some (fanBlockRows 59)),(21,some (fanBlockRows 59)),(22,some (fanBlockRows 59)),(23,some (fanBlockRows 2900)),(24,some (fanBlockRows 2901)),(25,some (fanBlockRows 2902)),(26,some (fanBlockRows 2903)),(27,some (fanBlockRows 2904)),(28,some (fanBlockRows 2905)),(29,some (fanBlockRows 2906)),(30,some (fanBlockRows 2907)),(31,some (fanBlockRows 2908)),(32,some (fanBlockRows 2909)),(33,none),(34,none),(35,none),(36,none),(37,none),(38,none),(39,none),(40,some (fanBlockRows 2910)),(41,some (fanBlockRows 2911)),(42,some (fanBlockRows 2912)),(43,some (fanBlockRows 2913)),(44,some (fanBlockRows 2914)),(45,some (fanBlockRows 2915)),(46,some (fanBlockRows 2916)),(47,some (fanBlockRows 2917)),(48,some (fanBlockRows 2918)),(49,some (fanBlockRows 2919)),(50,some (fanBlockRows 2920)),(51,some (fanBlockRows 2921)),(52,some (fanBlockRows 2922)),(53,some (fanBlockRows 2923)),(54,some (fanBlockRows 2924)),(55,some (fanBlockRows 2925)),(56,some (fanBlockRows 2926)),(57,some (fanBlockRows 2927)),(58,some (fanBlockRows 2928)),(59,some (fanBlockRows 2929)),(60,some (fanBlockRows 2930)),(61,some (fanBlockRows 2931)),(62,some (fanBlockRows 2932)),(63,some (fanBlockRows 2933))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step18.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 63).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain5_15Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step18.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step18.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain5_15Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain5_15Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step18

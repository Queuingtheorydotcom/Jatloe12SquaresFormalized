import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step19
import Compact.HistoricalCommon.C701.Step19Groups00
import Compact.HistoricalCommon.C701.Step19Groups01
import Compact.HistoricalCommon.C701.Step19Groups02
import Compact.HistoricalCommon.C701.Step19Groups03
import Compact.HistoricalCommon.C701.Step19Groups04
import Compact.HistoricalCommon.C701.Step19Groups05
import Compact.HistoricalCommon.C701.Step19Groups06
import Compact.HistoricalCommon.C701.Step19Groups07
import Compact.HistoricalCommon.C701.Step19Groups08
import Compact.HistoricalCommon.C701.Step19Groups09
import Compact.HistoricalCommon.C701.Step19Groups10
import Compact.HistoricalCommon.C701.Step19Groups11

namespace N12Compact.HistoricalCommon.C701.Step19
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
  (.sourceCut 13 (.neighborCut 6 (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf)) (.neighborCut 3 (.sourceCut 6 .leaf .leaf) (.neighborCut 4 (.sourceCut 6 .leaf (.neighborCut 2 .leaf .leaf)) (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 7 .leaf (.sourceCut 6 (.neighborCut 13 .leaf (.neighborCut 6 .leaf .leaf)) (.neighborCut 6 .leaf (.neighborCut 7 (.sourceCut 3 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf .leaf))))))))))))) (.neighborCut 13 (.sourceCut 3 .leaf (.sourceCut 2 .leaf (.sourceCut 2 (.neighborCut 6 .leaf .leaf) (.neighborCut 3 .leaf (.neighborCut 3 .leaf .leaf))))) (.neighborCut 6 (.sourceCut 3 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 7 .leaf (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.sourceCut 3 (.neighborCut 6 .leaf .leaf) (.sourceCut 2 (.neighborCut 6 .leaf .leaf) (.neighborCut 6 .leaf .leaf)))))) (.neighborCut 13 .leaf (.sourceCut 3 (.neighborCut 6 .leaf .leaf) .leaf)))))))

theorem partition_checked : partition.Check ⟨0,27,0,52⟩ scopes := by decide +kernel

theorem covered (i : Fin 27) (j : Fin 52) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 27) (j : Fin 52) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context913_header,context914_header,context915_header,context916_header,context917_header,context918_header,context919_header,context920_header,context842_header,context895_header,context896_header,context897_header,context898_header,context899_header,context900_header,context901_header,context902_header,context903_header,context904_header,context905_header,context906_header,context907_header,context908_header,context909_header,context910_header,context911_header,context912_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 27).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(128,none),(129,none),(130,some (fanBlockRows 375)),(131,some (fanBlockRows 376)),(132,some (fanBlockRows 377)),(133,some (fanBlockRows 378)),(134,some (fanBlockRows 379)),(135,some (fanBlockRows 380)),(136,some (fanBlockRows 381)),(137,some (fanBlockRows 382)),(138,some (fanBlockRows 361)),(139,some (fanBlockRows 362)),(140,some (fanBlockRows 363)),(141,some (fanBlockRows 364)),(142,some (fanBlockRows 365)),(143,some (fanBlockRows 59)),(144,some (fanBlockRows 59)),(145,some (fanBlockRows 59)),(146,some (fanBlockRows 59)),(147,some (fanBlockRows 59)),(148,some (fanBlockRows 366)),(149,some (fanBlockRows 367)),(150,some (fanBlockRows 368)),(151,some (fanBlockRows 369)),(152,some (fanBlockRows 370)),(153,some (fanBlockRows 371)),(154,some (fanBlockRows 372)),(155,some (fanBlockRows 373)),(156,some (fanBlockRows 374)),(157,none),(158,none),(159,none),(160,none),(161,none),(162,none),(163,none),(164,none),(165,none),(166,none),(167,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step19.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 52).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain9_17Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step19.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step19.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain9_17Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain9_17Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step19

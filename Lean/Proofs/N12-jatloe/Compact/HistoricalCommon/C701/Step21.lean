import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step21
import Compact.HistoricalCommon.C701.Step21Groups00
import Compact.HistoricalCommon.C701.Step21Groups01
import Compact.HistoricalCommon.C701.Step21Groups02
import Compact.HistoricalCommon.C701.Step21Groups03

namespace N12Compact.HistoricalCommon.C701.Step21
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 5 (.neighborCut 5 (.sourceCut 2 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf))) .leaf) (.sourceCut 6 (.neighborCut 5 .leaf (.neighborCut 2 .leaf .leaf)) (.sourceCut 11 .leaf (.sourceCut 11 .leaf (.sourceCut 6 .leaf (.sourceCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,45,0,10⟩ scopes := by decide +kernel

theorem covered (i : Fin 45) (j : Fin 10) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 45) (j : Fin 10) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context921_header,context932_header,context943_header,context954_header,context960_header,context961_header,context962_header,context963_header,context964_header,context965_header,context922_header,context923_header,context924_header,context925_header,context926_header,context927_header,context928_header,context929_header,context930_header,context931_header,context933_header,context934_header,context935_header,context936_header,context937_header,context938_header,context939_header,context940_header,context941_header,context942_header,context944_header,context945_header,context946_header,context947_header,context948_header,context949_header,context950_header,context951_header,context952_header,context953_header,context955_header,context956_header,context957_header,context958_header,context959_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 45).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(641,some (fanBlockRows 383)),(642,some (fanBlockRows 384)),(643,some (fanBlockRows 385)),(644,some (fanBlockRows 386)),(645,some (fanBlockRows 390)),(646,some (fanBlockRows 391)),(647,some (fanBlockRows 59)),(648,some (fanBlockRows 59)),(649,some (fanBlockRows 59)),(650,some (fanBlockRows 59)),(651,some (fanBlockRows 59)),(652,some (fanBlockRows 59)),(653,some (fanBlockRows 59)),(654,some (fanBlockRows 59)),(655,some (fanBlockRows 59)),(656,some (fanBlockRows 59)),(657,some (fanBlockRows 59)),(658,some (fanBlockRows 59)),(659,some (fanBlockRows 59)),(660,some (fanBlockRows 59)),(661,some (fanBlockRows 59)),(662,some (fanBlockRows 59)),(663,some (fanBlockRows 59)),(664,some (fanBlockRows 59)),(665,some (fanBlockRows 59)),(666,some (fanBlockRows 59)),(667,some (fanBlockRows 59)),(668,some (fanBlockRows 59)),(669,some (fanBlockRows 59)),(670,some (fanBlockRows 59)),(671,some (fanBlockRows 59)),(672,some (fanBlockRows 59)),(673,some (fanBlockRows 59)),(674,some (fanBlockRows 59)),(675,some (fanBlockRows 59)),(676,some (fanBlockRows 59)),(677,some (fanBlockRows 59)),(678,some (fanBlockRows 59)),(679,some (fanBlockRows 59)),(680,some (fanBlockRows 59)),(681,some (fanBlockRows 59)),(682,some (fanBlockRows 59)),(683,some (fanBlockRows 387)),(684,some (fanBlockRows 388)),(685,some (fanBlockRows 389))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step21.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 10).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain6_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step21.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step21.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain6_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain6_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step21

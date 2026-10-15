import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step26
import Compact.HistoricalCommon.C701.Step26Groups00
import Compact.HistoricalCommon.C701.Step26Groups01
import Compact.HistoricalCommon.C701.Step26Groups02
import Compact.HistoricalCommon.C701.Step26Groups03
import Compact.HistoricalCommon.C701.Step26Groups04

namespace N12Compact.HistoricalCommon.C701.Step26
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 6 (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 2 .leaf .leaf)))) (.sourceCut 7 (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))) (.sourceCut 13 (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))) (.sourceCut 6 (.neighborCut 3 .leaf (.sourceCut 1 .leaf (.sourceCut 2 .leaf .leaf))) (.sourceCut 7 .leaf .leaf)))))

theorem partition_checked : partition.Check ⟨0,52,0,7⟩ scopes := by decide +kernel

theorem covered (i : Fin 52) (j : Fin 7) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 52) (j : Fin 7) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1147_header,context1165_header,context1176_header,context1187_header,context1198_header,context1201_header,context1202_header,context1203_header,context1204_header,context1205_header,context1155_header,context1156_header,context1157_header,context1158_header,context1159_header,context1160_header,context1161_header,context1162_header,context1163_header,context1164_header,context1166_header,context1167_header,context1168_header,context1169_header,context1170_header,context1171_header,context1172_header,context1173_header,context1174_header,context1175_header,context1177_header,context1178_header,context1179_header,context1180_header,context1181_header,context1182_header,context1183_header,context1184_header,context1185_header,context1186_header,context1188_header,context1189_header,context1190_header,context1191_header,context1192_header,context1193_header,context1194_header,context1195_header,context1196_header,context1197_header,context1199_header,context1200_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 52).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(430,some (fanBlockRows 59)),(431,some (fanBlockRows 59)),(432,some (fanBlockRows 59)),(433,some (fanBlockRows 59)),(434,some (fanBlockRows 471)),(435,some (fanBlockRows 472)),(436,some (fanBlockRows 473)),(437,some (fanBlockRows 474)),(438,some (fanBlockRows 475)),(439,some (fanBlockRows 476)),(440,some (fanBlockRows 456)),(441,some (fanBlockRows 457)),(442,some (fanBlockRows 458)),(443,some (fanBlockRows 459)),(444,some (fanBlockRows 460)),(445,some (fanBlockRows 461)),(446,some (fanBlockRows 462)),(447,some (fanBlockRows 463)),(448,some (fanBlockRows 464)),(449,some (fanBlockRows 465)),(450,some (fanBlockRows 466)),(451,some (fanBlockRows 467)),(452,some (fanBlockRows 468)),(453,some (fanBlockRows 469)),(454,some (fanBlockRows 470)),(455,some (fanBlockRows 59)),(456,some (fanBlockRows 59)),(457,some (fanBlockRows 59)),(458,some (fanBlockRows 59)),(459,some (fanBlockRows 59)),(460,some (fanBlockRows 59)),(461,some (fanBlockRows 59)),(462,some (fanBlockRows 59)),(463,some (fanBlockRows 59)),(464,some (fanBlockRows 59)),(465,some (fanBlockRows 59)),(466,some (fanBlockRows 59)),(467,some (fanBlockRows 59)),(468,some (fanBlockRows 59)),(469,some (fanBlockRows 59)),(470,some (fanBlockRows 59)),(471,some (fanBlockRows 59)),(472,some (fanBlockRows 59)),(473,some (fanBlockRows 59)),(474,some (fanBlockRows 59)),(475,some (fanBlockRows 59)),(476,some (fanBlockRows 59)),(477,some (fanBlockRows 59)),(478,some (fanBlockRows 59)),(479,some (fanBlockRows 59)),(480,some (fanBlockRows 59)),(481,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step26.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 7).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain7_24Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step26.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step26.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain7_24Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain7_24Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step26

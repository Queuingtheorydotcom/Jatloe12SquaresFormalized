import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step22
import Compact.HistoricalCommon.C701.Step22Groups00
import Compact.HistoricalCommon.C701.Step22Groups01
import Compact.HistoricalCommon.C701.Step22Groups02
import Compact.HistoricalCommon.C701.Step22Groups03
import Compact.HistoricalCommon.C701.Step22Groups04
import Compact.HistoricalCommon.C701.Step22Groups05

namespace N12Compact.HistoricalCommon.C701.Step22
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 8 (.neighborCut 3 (.sourceCut 4 .leaf .leaf) (.neighborCut 3 (.sourceCut 4 .leaf (.neighborCut 1 .leaf .leaf)) .leaf)) (.sourceCut 8 (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf .leaf)))) (.sourceCut 8 (.neighborCut 6 .leaf (.sourceCut 2 .leaf (.sourceCut 2 .leaf (.sourceCut 2 .leaf .leaf)))) (.sourceCut 8 .leaf (.sourceCut 16 .leaf (.neighborCut 6 (.sourceCut 8 .leaf (.sourceCut 4 (.neighborCut 3 .leaf (.sourceCut 2 .leaf .leaf)) .leaf)) .leaf))))))

theorem partition_checked : partition.Check ⟨0,64,0,13⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 13) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 13) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context966_header,context977_header,context988_header,context999_header,context1010_header,context1021_header,context1026_header,context1027_header,context1028_header,context1029_header,context967_header,context968_header,context969_header,context970_header,context971_header,context972_header,context973_header,context974_header,context975_header,context976_header,context978_header,context979_header,context980_header,context981_header,context982_header,context983_header,context984_header,context985_header,context986_header,context987_header,context989_header,context990_header,context991_header,context992_header,context993_header,context994_header,context995_header,context996_header,context997_header,context998_header,context1000_header,context1001_header,context1002_header,context1003_header,context1004_header,context1005_header,context1006_header,context1007_header,context1008_header,context1009_header,context1011_header,context1012_header,context1013_header,context1014_header,context1015_header,context1016_header,context1017_header,context1018_header,context1019_header,context1020_header,context1022_header,context1023_header,context1024_header,context1025_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1038,some (fanBlockRows 392)),(1039,some (fanBlockRows 401)),(1040,some (fanBlockRows 402)),(1041,some (fanBlockRows 403)),(1042,some (fanBlockRows 404)),(1043,some (fanBlockRows 406)),(1044,some (fanBlockRows 411)),(1045,some (fanBlockRows 412)),(1046,some (fanBlockRows 413)),(1047,some (fanBlockRows 414)),(1048,some (fanBlockRows 59)),(1049,some (fanBlockRows 59)),(1050,some (fanBlockRows 393)),(1051,some (fanBlockRows 394)),(1052,some (fanBlockRows 395)),(1053,some (fanBlockRows 396)),(1054,some (fanBlockRows 397)),(1055,some (fanBlockRows 398)),(1056,some (fanBlockRows 399)),(1057,some (fanBlockRows 400)),(1058,some (fanBlockRows 59)),(1059,some (fanBlockRows 59)),(1060,some (fanBlockRows 59)),(1061,some (fanBlockRows 59)),(1062,some (fanBlockRows 59)),(1063,some (fanBlockRows 59)),(1064,some (fanBlockRows 59)),(1065,some (fanBlockRows 59)),(1066,some (fanBlockRows 59)),(1067,some (fanBlockRows 59)),(1068,some (fanBlockRows 59)),(1069,some (fanBlockRows 59)),(1070,some (fanBlockRows 59)),(1071,some (fanBlockRows 59)),(1072,some (fanBlockRows 59)),(1073,some (fanBlockRows 59)),(1074,some (fanBlockRows 59)),(1075,some (fanBlockRows 59)),(1076,some (fanBlockRows 59)),(1077,some (fanBlockRows 59)),(1078,some (fanBlockRows 59)),(1079,some (fanBlockRows 59)),(1080,some (fanBlockRows 59)),(1081,some (fanBlockRows 59)),(1082,some (fanBlockRows 59)),(1083,some (fanBlockRows 59)),(1084,some (fanBlockRows 59)),(1085,some (fanBlockRows 59)),(1086,some (fanBlockRows 59)),(1087,some (fanBlockRows 59)),(1088,some (fanBlockRows 59)),(1089,some (fanBlockRows 59)),(1090,some (fanBlockRows 59)),(1091,some (fanBlockRows 59)),(1092,some (fanBlockRows 59)),(1093,some (fanBlockRows 59)),(1094,some (fanBlockRows 59)),(1095,some (fanBlockRows 59)),(1096,some (fanBlockRows 59)),(1097,some (fanBlockRows 405)),(1098,some (fanBlockRows 407)),(1099,some (fanBlockRows 408)),(1100,some (fanBlockRows 409)),(1101,some (fanBlockRows 410))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step22.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 13).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain7_14Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step22.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step22.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain7_14Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain7_14Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step22

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step16
import Compact.HistoricalCommon.C973.Step16Groups00
import Compact.HistoricalCommon.C973.Step16Groups01
import Compact.HistoricalCommon.C973.Step16Groups02
import Compact.HistoricalCommon.C973.Step16Groups03
import Compact.HistoricalCommon.C973.Step16Groups04
import Compact.HistoricalCommon.C973.Step16Groups05
import Compact.HistoricalCommon.C973.Step16Groups06
import Compact.HistoricalCommon.C973.Step16Groups07
import Compact.HistoricalCommon.C973.Step16Groups08

namespace N12Compact.HistoricalCommon.C973.Step16
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 8 (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 4 .leaf .leaf))) (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 4 .leaf .leaf) .leaf)))) (.sourceCut 16 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 8 .leaf .leaf) (.neighborCut 8 (.sourceCut 8 .leaf .leaf) .leaf)))) (.sourceCut 16 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf .leaf))) (.sourceCut 8 (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)))) (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 4 .leaf .leaf) (.neighborCut 16 (.sourceCut 4 .leaf .leaf) (.neighborCut 16 (.sourceCut 4 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6961_header,context6972_header,context6983_header,context6994_header,context7005_header,context7016_header,context7021_header,context7022_header,context7023_header,context7024_header,context6962_header,context6963_header,context6964_header,context6965_header,context6966_header,context6967_header,context6968_header,context6969_header,context6970_header,context6971_header,context6973_header,context6974_header,context6975_header,context6976_header,context6977_header,context6978_header,context6979_header,context6980_header,context6981_header,context6982_header,context6984_header,context6985_header,context6986_header,context6987_header,context6988_header,context6989_header,context6990_header,context6991_header,context6992_header,context6993_header,context6995_header,context6996_header,context6997_header,context6998_header,context6999_header,context7000_header,context7001_header,context7002_header,context7003_header,context7004_header,context7006_header,context7007_header,context7008_header,context7009_header,context7010_header,context7011_header,context7012_header,context7013_header,context7014_header,context7015_header,context7017_header,context7018_header,context7019_header,context7020_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6030,some (fanBlockRows 2788)),(6031,some (fanBlockRows 2799)),(6032,some (fanBlockRows 2810)),(6033,some (fanBlockRows 2812)),(6034,some (fanBlockRows 2813)),(6035,some (fanBlockRows 2824)),(6036,some (fanBlockRows 2829)),(6037,some (fanBlockRows 2830)),(6038,some (fanBlockRows 2831)),(6039,some (fanBlockRows 2832)),(6040,some (fanBlockRows 2789)),(6041,some (fanBlockRows 2790)),(6042,some (fanBlockRows 2791)),(6043,some (fanBlockRows 2792)),(6044,some (fanBlockRows 2793)),(6045,some (fanBlockRows 2794)),(6046,some (fanBlockRows 2795)),(6047,some (fanBlockRows 2796)),(6048,some (fanBlockRows 2797)),(6049,some (fanBlockRows 2798)),(6050,some (fanBlockRows 2800)),(6051,some (fanBlockRows 2801)),(6052,some (fanBlockRows 2802)),(6053,some (fanBlockRows 2803)),(6054,some (fanBlockRows 2804)),(6055,some (fanBlockRows 2805)),(6056,some (fanBlockRows 2806)),(6057,some (fanBlockRows 2807)),(6058,some (fanBlockRows 2808)),(6059,some (fanBlockRows 2809)),(6060,some (fanBlockRows 2811)),(6061,some (fanBlockRows 59)),(6062,some (fanBlockRows 59)),(6063,some (fanBlockRows 59)),(6064,some (fanBlockRows 59)),(6065,some (fanBlockRows 59)),(6066,some (fanBlockRows 59)),(6067,some (fanBlockRows 59)),(6068,some (fanBlockRows 59)),(6069,some (fanBlockRows 59)),(6070,some (fanBlockRows 59)),(6071,some (fanBlockRows 59)),(6072,some (fanBlockRows 59)),(6073,some (fanBlockRows 59)),(6074,some (fanBlockRows 59)),(6075,some (fanBlockRows 59)),(6076,some (fanBlockRows 59)),(6077,some (fanBlockRows 59)),(6078,some (fanBlockRows 59)),(6079,some (fanBlockRows 59)),(6080,some (fanBlockRows 2814)),(6081,some (fanBlockRows 2815)),(6082,some (fanBlockRows 2816)),(6083,some (fanBlockRows 2817)),(6084,some (fanBlockRows 2818)),(6085,some (fanBlockRows 2819)),(6086,some (fanBlockRows 2820)),(6087,some (fanBlockRows 2821)),(6088,some (fanBlockRows 2822)),(6089,some (fanBlockRows 2823)),(6090,some (fanBlockRows 2825)),(6091,some (fanBlockRows 2826)),(6092,some (fanBlockRows 2827)),(6093,some (fanBlockRows 2828))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step16.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain7_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step16.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step16.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain7_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain7_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step16

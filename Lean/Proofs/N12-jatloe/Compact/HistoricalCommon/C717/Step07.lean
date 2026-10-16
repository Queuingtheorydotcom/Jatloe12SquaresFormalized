import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step07
import Compact.HistoricalCommon.C717.Step07Groups00
import Compact.HistoricalCommon.C717.Step07Groups01
import Compact.HistoricalCommon.C717.Step07Groups02
import Compact.HistoricalCommon.C717.Step07Groups03
import Compact.HistoricalCommon.C717.Step07Groups04
import Compact.HistoricalCommon.C717.Step07Groups05

namespace N12Compact.HistoricalCommon.C717.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 30 (.neighborCut 28 (.sourceCut 15 (.neighborCut 14 (.sourceCut 7 .leaf .leaf) .leaf) (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf))) (.neighborCut 29 (.sourceCut 15 .leaf (.sourceCut 7 .leaf .leaf)) .leaf)) (.sourceCut 15 (.neighborCut 28 (.sourceCut 7 .leaf .leaf) (.neighborCut 29 (.sourceCut 3 .leaf (.sourceCut 4 .leaf .leaf)) .leaf)) (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 29 .leaf (.sourceCut 7 .leaf .leaf)))))))

theorem partition_checked : partition.Check ⟨0,60,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 60) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 60) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6121_header,context6127_header,context6128_header,context6129_header,context6130_header,context6071_header,context6072_header,context6073_header,context6074_header,context6075_header,context6076_header,context6077_header,context6078_header,context6079_header,context6080_header,context6081_header,context6082_header,context6083_header,context6084_header,context6085_header,context6086_header,context6087_header,context6088_header,context6089_header,context6090_header,context6091_header,context6092_header,context6093_header,context6094_header,context6095_header,context6096_header,context6097_header,context6098_header,context6099_header,context6100_header,context6101_header,context6102_header,context6103_header,context6104_header,context6105_header,context6106_header,context6107_header,context6108_header,context6109_header,context6110_header,context6111_header,context6112_header,context6113_header,context6114_header,context6115_header,context6116_header,context6117_header,context6118_header,context6119_header,context6120_header,context6122_header,context6123_header,context6124_header,context6125_header,context6126_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 60).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5403,none),(5404,none),(5405,none),(5406,none),(5407,none),(5408,some (fanBlockRows 2406)),(5409,some (fanBlockRows 2407)),(5410,some (fanBlockRows 2408)),(5411,some (fanBlockRows 2409)),(5412,some (fanBlockRows 2410)),(5413,some (fanBlockRows 2391)),(5414,some (fanBlockRows 2392)),(5415,some (fanBlockRows 2393)),(5416,some (fanBlockRows 2394)),(5417,some (fanBlockRows 2395)),(5418,some (fanBlockRows 2396)),(5419,some (fanBlockRows 2397)),(5420,some (fanBlockRows 2398)),(5421,some (fanBlockRows 59)),(5422,some (fanBlockRows 59)),(5423,some (fanBlockRows 59)),(5424,some (fanBlockRows 59)),(5425,some (fanBlockRows 59)),(5426,some (fanBlockRows 59)),(5427,some (fanBlockRows 59)),(5428,some (fanBlockRows 59)),(5429,some (fanBlockRows 59)),(5430,some (fanBlockRows 59)),(5431,some (fanBlockRows 59)),(5432,some (fanBlockRows 2399)),(5433,some (fanBlockRows 2400)),(5434,some (fanBlockRows 2401)),(5435,some (fanBlockRows 2402)),(5436,some (fanBlockRows 2403)),(5437,some (fanBlockRows 2404)),(5438,some (fanBlockRows 2405)),(5439,some (fanBlockRows 59)),(5440,some (fanBlockRows 59)),(5441,some (fanBlockRows 59)),(5442,some (fanBlockRows 59)),(5443,some (fanBlockRows 59)),(5444,some (fanBlockRows 59)),(5445,some (fanBlockRows 59)),(5446,some (fanBlockRows 59)),(5447,some (fanBlockRows 59)),(5448,some (fanBlockRows 59)),(5449,some (fanBlockRows 59)),(5450,some (fanBlockRows 59)),(5451,some (fanBlockRows 59)),(5452,some (fanBlockRows 59)),(5453,some (fanBlockRows 59)),(5454,some (fanBlockRows 59)),(5455,some (fanBlockRows 59)),(5456,some (fanBlockRows 59)),(5457,some (fanBlockRows 59)),(5458,some (fanBlockRows 59)),(5459,some (fanBlockRows 59)),(5460,some (fanBlockRows 59)),(5461,some (fanBlockRows 59)),(5462,some (fanBlockRows 59)),(5463,some (fanBlockRows 59)),(5464,some (fanBlockRows 59)),(5465,some (fanBlockRows 59)),(5466,some (fanBlockRows 59)),(5467,some (fanBlockRows 59)),(5468,none),(5469,none)]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step07.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step07.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step07.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step07

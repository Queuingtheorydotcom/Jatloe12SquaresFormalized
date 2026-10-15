import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step23
import Compact.HistoricalCommon.C973.Step23Groups00
import Compact.HistoricalCommon.C973.Step23Groups01
import Compact.HistoricalCommon.C973.Step23Groups02
import Compact.HistoricalCommon.C973.Step23Groups03
import Compact.HistoricalCommon.C973.Step23Groups04
import Compact.HistoricalCommon.C973.Step23Groups05

namespace N12Compact.HistoricalCommon.C973.Step23
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
  (.sourceCut 8 (.neighborCut 5 .leaf (.neighborCut 6 .leaf (.neighborCut 11 .leaf (.neighborCut 11 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf)))))) (.sourceCut 8 .leaf (.sourceCut 16 .leaf (.neighborCut 22 (.sourceCut 16 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 6 .leaf .leaf)))) (.neighborCut 11 .leaf (.neighborCut 6 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf (.sourceCut 4 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,64,0,45⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 45) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 45) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7816_header,context7872_header,context7883_header,context7894_header,context7905_header,context7916_header,context7921_header,context7922_header,context7923_header,context7924_header,context7862_header,context7863_header,context7864_header,context7865_header,context7866_header,context7867_header,context7868_header,context7869_header,context7870_header,context7871_header,context7873_header,context7874_header,context7875_header,context7876_header,context7877_header,context7878_header,context7879_header,context7880_header,context7881_header,context7882_header,context7884_header,context7885_header,context7886_header,context7887_header,context7888_header,context7889_header,context7890_header,context7891_header,context7892_header,context7893_header,context7895_header,context7896_header,context7897_header,context7898_header,context7899_header,context7900_header,context7901_header,context7902_header,context7903_header,context7904_header,context7906_header,context7907_header,context7908_header,context7909_header,context7910_header,context7911_header,context7912_header,context7913_header,context7914_header,context7915_header,context7917_header,context7918_header,context7919_header,context7920_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6957,some (fanBlockRows 3187)),(6958,some (fanBlockRows 3188)),(6959,some (fanBlockRows 3189)),(6960,some (fanBlockRows 3190)),(6961,some (fanBlockRows 3191)),(6962,some (fanBlockRows 3192)),(6963,some (fanBlockRows 59)),(6964,some (fanBlockRows 59)),(6965,some (fanBlockRows 59)),(6966,some (fanBlockRows 59)),(6967,some (fanBlockRows 59)),(6968,some (fanBlockRows 59)),(6969,some (fanBlockRows 59)),(6970,some (fanBlockRows 59)),(6971,some (fanBlockRows 59)),(6972,some (fanBlockRows 59)),(6973,some (fanBlockRows 59)),(6974,some (fanBlockRows 59)),(6975,some (fanBlockRows 59)),(6976,some (fanBlockRows 59)),(6977,some (fanBlockRows 59)),(6978,some (fanBlockRows 59)),(6979,some (fanBlockRows 59)),(6980,some (fanBlockRows 59)),(6981,some (fanBlockRows 59)),(6982,some (fanBlockRows 59)),(6983,some (fanBlockRows 59)),(6984,some (fanBlockRows 59)),(6985,some (fanBlockRows 59)),(6986,some (fanBlockRows 59)),(6987,some (fanBlockRows 59)),(6988,some (fanBlockRows 59)),(6989,some (fanBlockRows 59)),(6990,some (fanBlockRows 59)),(6991,some (fanBlockRows 59)),(6992,some (fanBlockRows 59)),(6993,some (fanBlockRows 59)),(6994,some (fanBlockRows 59)),(6995,some (fanBlockRows 59)),(6996,some (fanBlockRows 59)),(6997,some (fanBlockRows 59)),(6998,some (fanBlockRows 59)),(6999,some (fanBlockRows 59)),(7000,some (fanBlockRows 59)),(7001,some (fanBlockRows 59)),(7002,some (fanBlockRows 59)),(7003,some (fanBlockRows 59)),(7004,some (fanBlockRows 59)),(7005,some (fanBlockRows 59)),(7006,some (fanBlockRows 59)),(7007,some (fanBlockRows 59)),(7008,some (fanBlockRows 59)),(7009,some (fanBlockRows 59)),(7010,some (fanBlockRows 59)),(7011,some (fanBlockRows 59)),(7012,some (fanBlockRows 59)),(7013,some (fanBlockRows 59)),(7014,some (fanBlockRows 59)),(7015,some (fanBlockRows 59)),(7016,some (fanBlockRows 59)),(7017,some (fanBlockRows 59)),(7018,some (fanBlockRows 3193)),(7019,some (fanBlockRows 3194)),(7020,some (fanBlockRows 3195))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step23.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 45).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain10_17Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step23.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step23.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain10_17Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain10_17Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step23

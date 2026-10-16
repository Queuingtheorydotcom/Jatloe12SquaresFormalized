import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step18
import Compact.HistoricalCommon.C701.Step18Groups00
import Compact.HistoricalCommon.C701.Step18Groups01
import Compact.HistoricalCommon.C701.Step18Groups02
import Compact.HistoricalCommon.C701.Step18Groups03
import Compact.HistoricalCommon.C701.Step18Groups04
import Compact.HistoricalCommon.C701.Step18Groups05
import Compact.HistoricalCommon.C701.Step18Groups06
import Compact.HistoricalCommon.C701.Step18Groups07
import Compact.HistoricalCommon.C701.Step18Groups08
import Compact.HistoricalCommon.C701.Step18Groups09

namespace N12Compact.HistoricalCommon.C701.Step18
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 8 (.neighborCut 5 .leaf (.neighborCut 6 (.sourceCut 4 .leaf .leaf) (.neighborCut 5 .leaf (.neighborCut 6 .leaf (.neighborCut 11 .leaf .leaf))))) (.sourceCut 8 (.neighborCut 5 .leaf (.neighborCut 6 .leaf (.neighborCut 11 .leaf (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf))))) (.sourceCut 16 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 6 .leaf (.neighborCut 11 .leaf (.sourceCut 8 (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf)) .leaf))))) (.sourceCut 16 (.neighborCut 22 .leaf (.neighborCut 11 (.sourceCut 8 .leaf (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf))) .leaf)) (.sourceCut 8 (.neighborCut 22 .leaf (.neighborCut 11 (.sourceCut 4 .leaf .leaf) (.neighborCut 6 .leaf .leaf))) (.neighborCut 22 (.sourceCut 4 .leaf (.sourceCut 2 .leaf .leaf)) (.neighborCut 11 .leaf .leaf)))))))

theorem partition_checked : partition.Check ⟨0,64,0,45⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 45) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 45) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context754_header,context765_header,context786_header,context807_header,context822_header,context833_header,context838_header,context839_header,context840_header,context841_header,context755_header,context756_header,context757_header,context758_header,context759_header,context760_header,context761_header,context762_header,context763_header,context764_header,context767_header,context769_header,context771_header,context773_header,context775_header,context777_header,context779_header,context781_header,context783_header,context785_header,context788_header,context790_header,context792_header,context794_header,context796_header,context798_header,context800_header,context802_header,context804_header,context806_header,context809_header,context811_header,context813_header,context815_header,context816_header,context817_header,context818_header,context819_header,context820_header,context821_header,context823_header,context824_header,context825_header,context826_header,context827_header,context828_header,context829_header,context830_header,context831_header,context832_header,context834_header,context835_header,context836_header,context837_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(64,some (fanBlockRows 321)),(65,some (fanBlockRows 332)),(66,some (fanBlockRows 333)),(67,some (fanBlockRows 334)),(68,some (fanBlockRows 341)),(69,some (fanBlockRows 352)),(70,some (fanBlockRows 357)),(71,some (fanBlockRows 358)),(72,some (fanBlockRows 359)),(73,some (fanBlockRows 360)),(74,some (fanBlockRows 322)),(75,some (fanBlockRows 323)),(76,some (fanBlockRows 324)),(77,some (fanBlockRows 325)),(78,some (fanBlockRows 326)),(79,some (fanBlockRows 327)),(80,some (fanBlockRows 328)),(81,some (fanBlockRows 329)),(82,some (fanBlockRows 330)),(83,some (fanBlockRows 331)),(84,some (fanBlockRows 59)),(85,some (fanBlockRows 59)),(86,some (fanBlockRows 59)),(87,some (fanBlockRows 59)),(88,some (fanBlockRows 59)),(89,some (fanBlockRows 59)),(90,some (fanBlockRows 59)),(91,some (fanBlockRows 59)),(92,some (fanBlockRows 59)),(93,some (fanBlockRows 59)),(94,some (fanBlockRows 59)),(95,some (fanBlockRows 59)),(96,some (fanBlockRows 59)),(97,some (fanBlockRows 59)),(98,some (fanBlockRows 59)),(99,some (fanBlockRows 59)),(100,some (fanBlockRows 59)),(101,some (fanBlockRows 59)),(102,some (fanBlockRows 59)),(103,some (fanBlockRows 59)),(104,some (fanBlockRows 59)),(105,some (fanBlockRows 59)),(106,some (fanBlockRows 59)),(107,some (fanBlockRows 59)),(108,some (fanBlockRows 335)),(109,some (fanBlockRows 336)),(110,some (fanBlockRows 337)),(111,some (fanBlockRows 338)),(112,some (fanBlockRows 339)),(113,some (fanBlockRows 340)),(114,some (fanBlockRows 342)),(115,some (fanBlockRows 343)),(116,some (fanBlockRows 344)),(117,some (fanBlockRows 345)),(118,some (fanBlockRows 346)),(119,some (fanBlockRows 347)),(120,some (fanBlockRows 348)),(121,some (fanBlockRows 349)),(122,some (fanBlockRows 350)),(123,some (fanBlockRows 351)),(124,some (fanBlockRows 353)),(125,some (fanBlockRows 354)),(126,some (fanBlockRows 355)),(127,some (fanBlockRows 356))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step18.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 45).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain1_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step18.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step18.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain1_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain1_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step18

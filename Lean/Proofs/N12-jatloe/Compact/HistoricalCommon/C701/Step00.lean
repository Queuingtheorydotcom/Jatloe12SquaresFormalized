import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step00
import Compact.HistoricalCommon.C701.Step00Groups00
import Compact.HistoricalCommon.C701.Step00Groups01
import Compact.HistoricalCommon.C701.Step00Groups02
import Compact.HistoricalCommon.C701.Step00Groups03
import Compact.HistoricalCommon.C701.Step00Groups04
import Compact.HistoricalCommon.C701.Step00Groups05
import Compact.HistoricalCommon.C701.Step00Groups06
import Compact.HistoricalCommon.C701.Step00Groups07

namespace N12Compact.HistoricalCommon.C701.Step00
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 23 (.neighborCut 14 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 15 .leaf (.neighborCut 7 .leaf (.sourceCut 11 (.neighborCut 4 .leaf .leaf) (.sourceCut 6 (.neighborCut 4 .leaf .leaf) (.sourceCut 3 .leaf .leaf))))))))) (.neighborCut 7 (.sourceCut 12 .leaf (.sourceCut 6 .leaf (.neighborCut 3 .leaf .leaf))) (.neighborCut 7 (.sourceCut 6 .leaf (.sourceCut 6 (.neighborCut 3 .leaf .leaf) .leaf)) (.neighborCut 15 (.sourceCut 12 .leaf .leaf) (.neighborCut 15 .leaf (.sourceCut 12 .leaf (.sourceCut 6 (.neighborCut 7 .leaf .leaf) (.neighborCut 7 .leaf (.sourceCut 3 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,47,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 47) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 47) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context102_header,context103_header,context104_header,context105_header,context0_header,context60_header,context61_header,context62_header,context63_header,context64_header,context65_header,context66_header,context67_header,context68_header,context69_header,context70_header,context71_header,context72_header,context73_header,context74_header,context75_header,context76_header,context77_header,context78_header,context79_header,context80_header,context81_header,context82_header,context83_header,context84_header,context85_header,context86_header,context87_header,context88_header,context89_header,context90_header,context91_header,context92_header,context93_header,context94_header,context95_header,context96_header,context97_header,context98_header,context99_header,context100_header,context101_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 47).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(0,none),(1,none),(2,none),(3,none),(4,none),(5,none),(6,some (fanBlockRows 43)),(7,some (fanBlockRows 44)),(8,some (fanBlockRows 45)),(9,some (fanBlockRows 46)),(10,some (fanBlockRows 0)),(11,some (fanBlockRows 1)),(12,some (fanBlockRows 2)),(13,some (fanBlockRows 3)),(14,some (fanBlockRows 4)),(15,some (fanBlockRows 5)),(16,some (fanBlockRows 6)),(17,some (fanBlockRows 7)),(18,some (fanBlockRows 8)),(19,some (fanBlockRows 9)),(20,some (fanBlockRows 10)),(21,some (fanBlockRows 11)),(22,some (fanBlockRows 12)),(23,some (fanBlockRows 13)),(24,some (fanBlockRows 14)),(25,some (fanBlockRows 15)),(26,some (fanBlockRows 16)),(27,some (fanBlockRows 17)),(28,some (fanBlockRows 18)),(29,some (fanBlockRows 19)),(30,some (fanBlockRows 20)),(31,some (fanBlockRows 21)),(32,some (fanBlockRows 22)),(33,some (fanBlockRows 23)),(34,some (fanBlockRows 24)),(35,some (fanBlockRows 25)),(36,some (fanBlockRows 26)),(37,some (fanBlockRows 27)),(38,some (fanBlockRows 28)),(39,some (fanBlockRows 29)),(40,some (fanBlockRows 30)),(41,some (fanBlockRows 31)),(42,some (fanBlockRows 32)),(43,some (fanBlockRows 33)),(44,some (fanBlockRows 34)),(45,some (fanBlockRows 35)),(46,some (fanBlockRows 36)),(47,some (fanBlockRows 37)),(48,some (fanBlockRows 38)),(49,some (fanBlockRows 39)),(50,some (fanBlockRows 40)),(51,some (fanBlockRows 41)),(52,some (fanBlockRows 42)),(53,none),(54,none),(55,none),(56,none),(57,none),(58,none),(59,none),(60,none),(61,none),(62,none),(63,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step00.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step00.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step00.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step00

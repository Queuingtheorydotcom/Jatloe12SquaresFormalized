import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step03
import Compact.HistoricalCommon.C701.Step03Groups00
import Compact.HistoricalCommon.C701.Step03Groups01
import Compact.HistoricalCommon.C701.Step03Groups02
import Compact.HistoricalCommon.C701.Step03Groups03
import Compact.HistoricalCommon.C701.Step03Groups04
import Compact.HistoricalCommon.C701.Step03Groups05
import Compact.HistoricalCommon.C701.Step03Groups06
import Compact.HistoricalCommon.C701.Step03Groups07

namespace N12Compact.HistoricalCommon.C701.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 16 (.neighborCut 14 (.sourceCut 8 (.neighborCut 7 .leaf .leaf) .leaf) (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 15 .leaf .leaf))))) (.sourceCut 16 (.neighborCut 14 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 15 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))))))) (.neighborCut 14 (.sourceCut 8 (.neighborCut 7 .leaf .leaf) (.sourceCut 8 .leaf (.sourceCut 8 .leaf (.neighborCut 7 .leaf (.neighborCut 3 .leaf .leaf))))) (.neighborCut 15 .leaf (.sourceCut 16 (.neighborCut 15 (.sourceCut 8 .leaf (.neighborCut 7 .leaf .leaf)) .leaf) (.neighborCut 15 .leaf (.sourceCut 8 .leaf (.neighborCut 7 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,64,0,59⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 59) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 59) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context106_header,context117_header,context128_header,context139_header,context150_header,context161_header,context166_header,context167_header,context168_header,context169_header,context107_header,context108_header,context109_header,context110_header,context111_header,context112_header,context113_header,context114_header,context115_header,context116_header,context118_header,context119_header,context120_header,context121_header,context122_header,context123_header,context124_header,context125_header,context126_header,context127_header,context129_header,context130_header,context131_header,context132_header,context133_header,context134_header,context135_header,context136_header,context137_header,context138_header,context140_header,context141_header,context142_header,context143_header,context144_header,context145_header,context146_header,context147_header,context148_header,context149_header,context151_header,context152_header,context153_header,context154_header,context155_header,context156_header,context157_header,context158_header,context159_header,context160_header,context162_header,context163_header,context164_header,context165_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(740,some (fanBlockRows 47)),(741,some (fanBlockRows 58)),(742,some (fanBlockRows 60)),(743,some (fanBlockRows 67)),(744,some (fanBlockRows 78)),(745,some (fanBlockRows 89)),(746,some (fanBlockRows 94)),(747,some (fanBlockRows 95)),(748,some (fanBlockRows 96)),(749,some (fanBlockRows 97)),(750,some (fanBlockRows 48)),(751,some (fanBlockRows 49)),(752,some (fanBlockRows 50)),(753,some (fanBlockRows 51)),(754,some (fanBlockRows 52)),(755,some (fanBlockRows 53)),(756,some (fanBlockRows 54)),(757,some (fanBlockRows 55)),(758,some (fanBlockRows 56)),(759,some (fanBlockRows 57)),(760,some (fanBlockRows 59)),(761,some (fanBlockRows 59)),(762,some (fanBlockRows 59)),(763,some (fanBlockRows 59)),(764,some (fanBlockRows 59)),(765,some (fanBlockRows 59)),(766,some (fanBlockRows 59)),(767,some (fanBlockRows 59)),(768,some (fanBlockRows 59)),(769,some (fanBlockRows 59)),(770,some (fanBlockRows 59)),(771,some (fanBlockRows 59)),(772,some (fanBlockRows 59)),(773,some (fanBlockRows 59)),(774,some (fanBlockRows 61)),(775,some (fanBlockRows 62)),(776,some (fanBlockRows 63)),(777,some (fanBlockRows 64)),(778,some (fanBlockRows 65)),(779,some (fanBlockRows 66)),(780,some (fanBlockRows 68)),(781,some (fanBlockRows 69)),(782,some (fanBlockRows 70)),(783,some (fanBlockRows 71)),(784,some (fanBlockRows 72)),(785,some (fanBlockRows 73)),(786,some (fanBlockRows 74)),(787,some (fanBlockRows 75)),(788,some (fanBlockRows 76)),(789,some (fanBlockRows 77)),(790,some (fanBlockRows 79)),(791,some (fanBlockRows 80)),(792,some (fanBlockRows 81)),(793,some (fanBlockRows 82)),(794,some (fanBlockRows 83)),(795,some (fanBlockRows 84)),(796,some (fanBlockRows 85)),(797,some (fanBlockRows 86)),(798,some (fanBlockRows 87)),(799,some (fanBlockRows 88)),(800,some (fanBlockRows 90)),(801,some (fanBlockRows 91)),(802,some (fanBlockRows 92)),(803,some (fanBlockRows 93))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step03.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 59).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step03.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step03.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step03

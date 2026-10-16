import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step25
import Compact.HistoricalCommon.C979.Step25Groups00

namespace N12Compact.HistoricalCommon.C979.Step25
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0]

def scopes : List Scope :=
  [group0_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  .leaf

theorem partition_checked : partition.Check ⟨0,66,0,9⟩ scopes := by decide +kernel

theorem covered (i : Fin 66) (j : Fin 9) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 66) (j : Fin 9) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11640_header,context11660_header,context11671_header,context11682_header,context11693_header,context11704_header,context11711_header,context11712_header,context11713_header,context11714_header,context11650_header,context11651_header,context11652_header,context11653_header,context11654_header,context11655_header,context11656_header,context11657_header,context11658_header,context11659_header,context11661_header,context11662_header,context11663_header,context11664_header,context11665_header,context11666_header,context11667_header,context11668_header,context11669_header,context11670_header,context11672_header,context11673_header,context11674_header,context11675_header,context11676_header,context11677_header,context11678_header,context11679_header,context11680_header,context11681_header,context11683_header,context11684_header,context11685_header,context11686_header,context11687_header,context11688_header,context11689_header,context11690_header,context11691_header,context11692_header,context11694_header,context11695_header,context11696_header,context11697_header,context11698_header,context11699_header,context11700_header,context11701_header,context11702_header,context11703_header,context11705_header,context11706_header,context11707_header,context11708_header,context11709_header,context11710_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 66).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11970,some (fanBlockRows 4909)),(11971,some (fanBlockRows 59)),(11972,some (fanBlockRows 59)),(11973,some (fanBlockRows 59)),(11974,some (fanBlockRows 59)),(11975,some (fanBlockRows 59)),(11976,some (fanBlockRows 59)),(11977,some (fanBlockRows 59)),(11978,some (fanBlockRows 59)),(11979,some (fanBlockRows 59)),(11980,some (fanBlockRows 59)),(11981,some (fanBlockRows 59)),(11982,some (fanBlockRows 59)),(11983,some (fanBlockRows 59)),(11984,some (fanBlockRows 59)),(11985,some (fanBlockRows 59)),(11986,some (fanBlockRows 59)),(11987,some (fanBlockRows 59)),(11988,some (fanBlockRows 59)),(11989,some (fanBlockRows 59)),(11990,some (fanBlockRows 59)),(11991,some (fanBlockRows 59)),(11992,some (fanBlockRows 59)),(11993,some (fanBlockRows 59)),(11994,some (fanBlockRows 59)),(11995,some (fanBlockRows 4910)),(11996,some (fanBlockRows 4911)),(11997,some (fanBlockRows 4912)),(11998,some (fanBlockRows 4913)),(11999,some (fanBlockRows 4914)),(12000,some (fanBlockRows 4915)),(12001,some (fanBlockRows 4916)),(12002,some (fanBlockRows 4917)),(12003,some (fanBlockRows 4918)),(12004,some (fanBlockRows 4919)),(12005,some (fanBlockRows 4920)),(12006,some (fanBlockRows 4921)),(12007,some (fanBlockRows 4922)),(12008,some (fanBlockRows 4923)),(12009,some (fanBlockRows 4924)),(12010,some (fanBlockRows 4925)),(12011,some (fanBlockRows 4926)),(12012,some (fanBlockRows 4927)),(12013,some (fanBlockRows 4928)),(12014,some (fanBlockRows 4929)),(12015,some (fanBlockRows 4930)),(12016,some (fanBlockRows 4931)),(12017,some (fanBlockRows 4932)),(12018,some (fanBlockRows 4933)),(12019,some (fanBlockRows 4934)),(12020,some (fanBlockRows 4935)),(12021,some (fanBlockRows 4936)),(12022,some (fanBlockRows 4937)),(12023,some (fanBlockRows 4938)),(12024,some (fanBlockRows 4939)),(12025,some (fanBlockRows 4940)),(12026,some (fanBlockRows 4941)),(12027,some (fanBlockRows 4942)),(12028,some (fanBlockRows 4943)),(12029,some (fanBlockRows 4944)),(12030,some (fanBlockRows 4945)),(12031,some (fanBlockRows 4946)),(12032,some (fanBlockRows 4947)),(12033,some (fanBlockRows 4948)),(12034,some (fanBlockRows 4949)),(12035,some (fanBlockRows 4950))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step25.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 9).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain6_24Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step25.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step25.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain6_24Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain6_24Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step25

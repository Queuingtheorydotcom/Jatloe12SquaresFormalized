import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step22
import Compact.HistoricalCommon.C979.Step22Groups00

namespace N12Compact.HistoricalCommon.C979.Step22
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

theorem partition_checked : partition.Check ⟨0,92,0,29⟩ scopes := by decide +kernel

theorem covered (i : Fin 92) (j : Fin 29) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 92) (j : Fin 29) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11395_header,context11406_header,context11417_header,context11428_header,context11439_header,context11450_header,context11461_header,context11472_header,context11483_header,context11486_header,context11396_header,context11397_header,context11398_header,context11399_header,context11400_header,context11401_header,context11402_header,context11403_header,context11404_header,context11405_header,context11407_header,context11408_header,context11409_header,context11410_header,context11411_header,context11412_header,context11413_header,context11414_header,context11415_header,context11416_header,context11418_header,context11419_header,context11420_header,context11421_header,context11422_header,context11423_header,context11424_header,context11425_header,context11426_header,context11427_header,context11429_header,context11430_header,context11431_header,context11432_header,context11433_header,context11434_header,context11435_header,context11436_header,context11437_header,context11438_header,context11440_header,context11441_header,context11442_header,context11443_header,context11444_header,context11445_header,context11446_header,context11447_header,context11448_header,context11449_header,context11451_header,context11452_header,context11453_header,context11454_header,context11455_header,context11456_header,context11457_header,context11458_header,context11459_header,context11460_header,context11462_header,context11463_header,context11464_header,context11465_header,context11466_header,context11467_header,context11468_header,context11469_header,context11470_header,context11471_header,context11473_header,context11474_header,context11475_header,context11476_header,context11477_header,context11478_header,context11479_header,context11480_header,context11481_header,context11482_header,context11484_header,context11485_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 92).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11367,some (fanBlockRows 4875)),(11368,some (fanBlockRows 4876)),(11369,some (fanBlockRows 4877)),(11370,some (fanBlockRows 4878)),(11371,some (fanBlockRows 4879)),(11372,some (fanBlockRows 59)),(11373,some (fanBlockRows 59)),(11374,some (fanBlockRows 59)),(11375,some (fanBlockRows 59)),(11376,some (fanBlockRows 59)),(11377,some (fanBlockRows 59)),(11378,some (fanBlockRows 59)),(11379,some (fanBlockRows 59)),(11380,some (fanBlockRows 59)),(11381,some (fanBlockRows 59)),(11382,some (fanBlockRows 59)),(11383,some (fanBlockRows 59)),(11384,some (fanBlockRows 59)),(11385,some (fanBlockRows 59)),(11386,some (fanBlockRows 59)),(11387,some (fanBlockRows 59)),(11388,some (fanBlockRows 59)),(11389,some (fanBlockRows 59)),(11390,some (fanBlockRows 59)),(11391,some (fanBlockRows 59)),(11392,some (fanBlockRows 59)),(11393,some (fanBlockRows 59)),(11394,some (fanBlockRows 59)),(11395,some (fanBlockRows 59)),(11396,some (fanBlockRows 59)),(11397,some (fanBlockRows 59)),(11398,some (fanBlockRows 59)),(11399,some (fanBlockRows 59)),(11400,some (fanBlockRows 59)),(11401,some (fanBlockRows 59)),(11402,some (fanBlockRows 59)),(11403,some (fanBlockRows 59)),(11404,some (fanBlockRows 59)),(11405,some (fanBlockRows 59)),(11406,some (fanBlockRows 59)),(11407,some (fanBlockRows 59)),(11408,some (fanBlockRows 59)),(11409,some (fanBlockRows 59)),(11410,some (fanBlockRows 59)),(11411,some (fanBlockRows 59)),(11412,some (fanBlockRows 59)),(11413,some (fanBlockRows 59)),(11414,some (fanBlockRows 59)),(11415,some (fanBlockRows 59)),(11416,some (fanBlockRows 59)),(11417,some (fanBlockRows 59)),(11418,some (fanBlockRows 59)),(11419,some (fanBlockRows 59)),(11420,some (fanBlockRows 59)),(11421,some (fanBlockRows 59)),(11422,some (fanBlockRows 59)),(11423,some (fanBlockRows 59)),(11424,some (fanBlockRows 59)),(11425,some (fanBlockRows 59)),(11426,some (fanBlockRows 4880)),(11427,some (fanBlockRows 4881)),(11428,some (fanBlockRows 4882)),(11429,some (fanBlockRows 4883)),(11430,some (fanBlockRows 4884)),(11431,some (fanBlockRows 4885)),(11432,some (fanBlockRows 4886)),(11433,some (fanBlockRows 4887)),(11434,some (fanBlockRows 4888)),(11435,some (fanBlockRows 4889)),(11436,some (fanBlockRows 4890)),(11437,some (fanBlockRows 4891)),(11438,some (fanBlockRows 4892)),(11439,some (fanBlockRows 4893)),(11440,some (fanBlockRows 4894)),(11441,some (fanBlockRows 4895)),(11442,some (fanBlockRows 4896)),(11443,some (fanBlockRows 4897)),(11444,some (fanBlockRows 4898)),(11445,some (fanBlockRows 59)),(11446,some (fanBlockRows 59)),(11447,some (fanBlockRows 59)),(11448,some (fanBlockRows 59)),(11449,some (fanBlockRows 59)),(11450,some (fanBlockRows 59)),(11451,some (fanBlockRows 59)),(11452,some (fanBlockRows 59)),(11453,some (fanBlockRows 4899)),(11454,some (fanBlockRows 59)),(11455,some (fanBlockRows 59)),(11456,some (fanBlockRows 59)),(11457,some (fanBlockRows 59)),(11458,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step22.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 29).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain7_16Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step22.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step22.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain7_16Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain7_16Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step22

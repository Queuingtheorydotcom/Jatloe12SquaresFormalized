import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step29
import Compact.HistoricalCommon.C979.Step29Groups00

namespace N12Compact.HistoricalCommon.C979.Step29
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

theorem partition_checked : partition.Check ⟨0,66,0,28⟩ scopes := by decide +kernel

theorem covered (i : Fin 66) (j : Fin 28) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 66) (j : Fin 28) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context11887_header,context11926_header,context11937_header,context11948_header,context11959_header,context11970_header,context11977_header,context11978_header,context11979_header,context11980_header,context11916_header,context11917_header,context11918_header,context11919_header,context11920_header,context11921_header,context11922_header,context11923_header,context11924_header,context11925_header,context11927_header,context11928_header,context11929_header,context11930_header,context11931_header,context11932_header,context11933_header,context11934_header,context11935_header,context11936_header,context11938_header,context11939_header,context11940_header,context11941_header,context11942_header,context11943_header,context11944_header,context11945_header,context11946_header,context11947_header,context11949_header,context11950_header,context11951_header,context11952_header,context11953_header,context11954_header,context11955_header,context11956_header,context11957_header,context11958_header,context11960_header,context11961_header,context11962_header,context11963_header,context11964_header,context11965_header,context11966_header,context11967_header,context11968_header,context11969_header,context11971_header,context11972_header,context11973_header,context11974_header,context11975_header,context11976_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 66).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(10322,some (fanBlockRows 59)),(10323,some (fanBlockRows 59)),(10324,some (fanBlockRows 59)),(10325,some (fanBlockRows 59)),(10326,some (fanBlockRows 59)),(10327,some (fanBlockRows 59)),(10328,some (fanBlockRows 59)),(10329,some (fanBlockRows 59)),(10330,some (fanBlockRows 59)),(10331,some (fanBlockRows 59)),(10332,some (fanBlockRows 59)),(10333,some (fanBlockRows 59)),(10334,some (fanBlockRows 59)),(10335,some (fanBlockRows 59)),(10336,some (fanBlockRows 59)),(10337,some (fanBlockRows 59)),(10338,some (fanBlockRows 59)),(10339,some (fanBlockRows 59)),(10340,some (fanBlockRows 59)),(10341,some (fanBlockRows 59)),(10342,some (fanBlockRows 59)),(10343,some (fanBlockRows 59)),(10344,some (fanBlockRows 59)),(10345,some (fanBlockRows 59)),(10346,some (fanBlockRows 59)),(10347,some (fanBlockRows 59)),(10348,some (fanBlockRows 59)),(10349,some (fanBlockRows 59)),(10350,some (fanBlockRows 59)),(10351,some (fanBlockRows 59)),(10352,some (fanBlockRows 59)),(10353,some (fanBlockRows 59)),(10354,some (fanBlockRows 59)),(10355,some (fanBlockRows 59)),(10356,some (fanBlockRows 59)),(10357,some (fanBlockRows 59)),(10358,some (fanBlockRows 59)),(10359,some (fanBlockRows 59)),(10360,some (fanBlockRows 59)),(10361,some (fanBlockRows 59)),(10362,some (fanBlockRows 59)),(10363,some (fanBlockRows 59)),(10364,some (fanBlockRows 59)),(10365,some (fanBlockRows 59)),(10366,some (fanBlockRows 59)),(10367,some (fanBlockRows 59)),(10368,some (fanBlockRows 59)),(10369,some (fanBlockRows 59)),(10370,some (fanBlockRows 59)),(10371,some (fanBlockRows 59)),(10372,some (fanBlockRows 59)),(10373,some (fanBlockRows 59)),(10374,some (fanBlockRows 59)),(10375,some (fanBlockRows 59)),(10376,some (fanBlockRows 59)),(10377,some (fanBlockRows 59)),(10378,some (fanBlockRows 59)),(10379,some (fanBlockRows 59)),(10380,some (fanBlockRows 59)),(10381,some (fanBlockRows 59)),(10382,some (fanBlockRows 59)),(10383,some (fanBlockRows 59)),(10384,some (fanBlockRows 59)),(10385,some (fanBlockRows 59)),(10386,some (fanBlockRows 59)),(10387,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step29.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 28).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain7_25Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step29.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step29.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain7_25Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain7_25Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step29

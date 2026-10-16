import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step18
import Compact.HistoricalCommon.C979.Step18Groups00

namespace N12Compact.HistoricalCommon.C979.Step18
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

theorem partition_checked : partition.Check ⟨0,128,0,29⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 29) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 29) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context10922_header,context10990_header,context11001_header,context11012_header,context11023_header,context11034_header,context11045_header,context11056_header,context11067_header,context11078_header,context10962_header,context10973_header,context10982_header,context10983_header,context10984_header,context10985_header,context10986_header,context10987_header,context10988_header,context10989_header,context10991_header,context10992_header,context10993_header,context10994_header,context10995_header,context10996_header,context10997_header,context10998_header,context10999_header,context11000_header,context11002_header,context11003_header,context11004_header,context11005_header,context11006_header,context11007_header,context11008_header,context11009_header,context11010_header,context11011_header,context11013_header,context11014_header,context11015_header,context11016_header,context11017_header,context11018_header,context11019_header,context11020_header,context11021_header,context11022_header,context11024_header,context11025_header,context11026_header,context11027_header,context11028_header,context11029_header,context11030_header,context11031_header,context11032_header,context11033_header,context11035_header,context11036_header,context11037_header,context11038_header,context11039_header,context11040_header,context11041_header,context11042_header,context11043_header,context11044_header,context11046_header,context11047_header,context11048_header,context11049_header,context11050_header,context11051_header,context11052_header,context11053_header,context11054_header,context11055_header,context11057_header,context11058_header,context11059_header,context11060_header,context11061_header,context11062_header,context11063_header,context11064_header,context11065_header,context11066_header,context11068_header,context11069_header,context11070_header,context11071_header,context11072_header,context11073_header,context11074_header,context11075_header,context11076_header,context11077_header,context10952_header,context10953_header,context10954_header,context10955_header,context10956_header,context10957_header,context10958_header,context10959_header,context10960_header,context10961_header,context10963_header,context10964_header,context10965_header,context10966_header,context10967_header,context10968_header,context10969_header,context10970_header,context10971_header,context10972_header,context10974_header,context10975_header,context10976_header,context10977_header,context10978_header,context10979_header,context10980_header,context10981_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(9057,some (fanBlockRows 4625)),(9058,some (fanBlockRows 4651)),(9059,some (fanBlockRows 59)),(9060,some (fanBlockRows 59)),(9061,some (fanBlockRows 59)),(9062,some (fanBlockRows 59)),(9063,some (fanBlockRows 59)),(9064,some (fanBlockRows 59)),(9065,some (fanBlockRows 59)),(9066,some (fanBlockRows 59)),(9067,some (fanBlockRows 59)),(9068,some (fanBlockRows 59)),(9069,some (fanBlockRows 59)),(9070,some (fanBlockRows 59)),(9071,some (fanBlockRows 59)),(9072,some (fanBlockRows 59)),(9073,some (fanBlockRows 59)),(9074,some (fanBlockRows 59)),(9075,some (fanBlockRows 59)),(9076,some (fanBlockRows 59)),(9077,some (fanBlockRows 59)),(9078,some (fanBlockRows 59)),(9079,some (fanBlockRows 59)),(9080,some (fanBlockRows 59)),(9081,some (fanBlockRows 59)),(9082,some (fanBlockRows 59)),(9083,some (fanBlockRows 59)),(9084,some (fanBlockRows 59)),(9085,some (fanBlockRows 59)),(9086,some (fanBlockRows 59)),(9087,some (fanBlockRows 59)),(9088,some (fanBlockRows 59)),(9089,some (fanBlockRows 59)),(9090,some (fanBlockRows 59)),(9091,some (fanBlockRows 59)),(9092,some (fanBlockRows 59)),(9093,some (fanBlockRows 59)),(9094,some (fanBlockRows 59)),(9095,some (fanBlockRows 59)),(9096,some (fanBlockRows 59)),(9097,some (fanBlockRows 59)),(9098,some (fanBlockRows 59)),(9099,some (fanBlockRows 59)),(9100,some (fanBlockRows 59)),(9101,some (fanBlockRows 59)),(9102,some (fanBlockRows 59)),(9103,some (fanBlockRows 59)),(9104,some (fanBlockRows 59)),(9105,some (fanBlockRows 59)),(9106,some (fanBlockRows 59)),(9107,some (fanBlockRows 59)),(9108,some (fanBlockRows 59)),(9109,some (fanBlockRows 59)),(9110,some (fanBlockRows 59)),(9111,some (fanBlockRows 59)),(9112,some (fanBlockRows 59)),(9113,some (fanBlockRows 59)),(9114,some (fanBlockRows 59)),(9115,some (fanBlockRows 59)),(9116,some (fanBlockRows 59)),(9117,some (fanBlockRows 59)),(9118,some (fanBlockRows 59)),(9119,some (fanBlockRows 59)),(9120,some (fanBlockRows 59)),(9121,some (fanBlockRows 59)),(9122,some (fanBlockRows 59)),(9123,some (fanBlockRows 59)),(9124,some (fanBlockRows 59)),(9125,some (fanBlockRows 59)),(9126,some (fanBlockRows 59)),(9127,some (fanBlockRows 59)),(9128,some (fanBlockRows 59)),(9129,some (fanBlockRows 59)),(9130,some (fanBlockRows 59)),(9131,some (fanBlockRows 59)),(9132,some (fanBlockRows 59)),(9133,some (fanBlockRows 59)),(9134,some (fanBlockRows 59)),(9135,some (fanBlockRows 59)),(9136,some (fanBlockRows 59)),(9137,some (fanBlockRows 59)),(9138,some (fanBlockRows 59)),(9139,some (fanBlockRows 59)),(9140,some (fanBlockRows 59)),(9141,some (fanBlockRows 59)),(9142,some (fanBlockRows 59)),(9143,some (fanBlockRows 59)),(9144,some (fanBlockRows 59)),(9145,some (fanBlockRows 59)),(9146,some (fanBlockRows 59)),(9147,some (fanBlockRows 59)),(9148,some (fanBlockRows 59)),(9149,some (fanBlockRows 59)),(9150,some (fanBlockRows 59)),(9151,some (fanBlockRows 59)),(9152,some (fanBlockRows 59)),(9153,some (fanBlockRows 59)),(9154,some (fanBlockRows 59)),(9155,some (fanBlockRows 59)),(9156,some (fanBlockRows 59)),(9157,some (fanBlockRows 59)),(9158,some (fanBlockRows 59)),(9159,some (fanBlockRows 59)),(9160,some (fanBlockRows 4626)),(9161,some (fanBlockRows 4627)),(9162,some (fanBlockRows 4628)),(9163,some (fanBlockRows 4629)),(9164,some (fanBlockRows 4630)),(9165,some (fanBlockRows 4631)),(9166,some (fanBlockRows 4632)),(9167,some (fanBlockRows 4633)),(9168,some (fanBlockRows 4634)),(9169,some (fanBlockRows 4635)),(9170,some (fanBlockRows 4636)),(9171,some (fanBlockRows 4637)),(9172,some (fanBlockRows 4638)),(9173,some (fanBlockRows 4639)),(9174,some (fanBlockRows 4640)),(9175,some (fanBlockRows 4641)),(9176,some (fanBlockRows 4642)),(9177,some (fanBlockRows 4643)),(9178,some (fanBlockRows 4644)),(9179,some (fanBlockRows 4645)),(9180,some (fanBlockRows 4646)),(9181,some (fanBlockRows 4647)),(9182,some (fanBlockRows 4648)),(9183,some (fanBlockRows 4649)),(9184,some (fanBlockRows 4650))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step18.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 29).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain7_16Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step18.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step18.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain7_16Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain7_16Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step18

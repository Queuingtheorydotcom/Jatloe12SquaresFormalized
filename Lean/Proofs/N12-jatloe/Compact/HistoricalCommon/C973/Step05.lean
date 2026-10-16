import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step05
import Compact.HistoricalCommon.C973.Step05Groups00
import Compact.HistoricalCommon.C973.Step05Groups01
import Compact.HistoricalCommon.C973.Step05Groups02
import Compact.HistoricalCommon.C973.Step05Groups03
import Compact.HistoricalCommon.C973.Step05Groups04
import Compact.HistoricalCommon.C973.Step05Groups05
import Compact.HistoricalCommon.C973.Step05Groups06
import Compact.HistoricalCommon.C973.Step05Groups07

namespace N12Compact.HistoricalCommon.C973.Step05
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)))))) (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 4 .leaf .leaf))))))) (.neighborCut 8 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 13 (.neighborCut 8 (.sourceCut 6 .leaf .leaf) (.neighborCut 4 .leaf .leaf)) .leaf) (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,53,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 53) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 53) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8376_header,context8377_header,context8378_header,context8326_header,context8327_header,context8328_header,context8329_header,context8330_header,context8331_header,context8332_header,context8333_header,context8334_header,context8335_header,context8336_header,context8337_header,context8338_header,context8339_header,context8340_header,context8341_header,context8342_header,context8343_header,context8344_header,context8345_header,context8346_header,context8347_header,context8348_header,context8349_header,context8350_header,context8351_header,context8352_header,context8353_header,context8354_header,context8355_header,context8356_header,context8357_header,context8358_header,context8359_header,context8360_header,context8361_header,context8362_header,context8363_header,context8364_header,context8365_header,context8366_header,context8367_header,context8368_header,context8369_header,context8370_header,context8371_header,context8372_header,context8373_header,context8374_header,context8375_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 53).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7094,none),(7095,none),(7096,none),(7097,none),(7098,none),(7099,none),(7100,none),(7101,some (fanBlockRows 3425)),(7102,some (fanBlockRows 3426)),(7103,some (fanBlockRows 3427)),(7104,some (fanBlockRows 3375)),(7105,some (fanBlockRows 3376)),(7106,some (fanBlockRows 3377)),(7107,some (fanBlockRows 3378)),(7108,some (fanBlockRows 3379)),(7109,some (fanBlockRows 3380)),(7110,some (fanBlockRows 3381)),(7111,some (fanBlockRows 3382)),(7112,some (fanBlockRows 3383)),(7113,some (fanBlockRows 3384)),(7114,some (fanBlockRows 3385)),(7115,some (fanBlockRows 3386)),(7116,some (fanBlockRows 3387)),(7117,some (fanBlockRows 3388)),(7118,some (fanBlockRows 3389)),(7119,some (fanBlockRows 3390)),(7120,some (fanBlockRows 3391)),(7121,some (fanBlockRows 3392)),(7122,some (fanBlockRows 3393)),(7123,some (fanBlockRows 3394)),(7124,some (fanBlockRows 3395)),(7125,some (fanBlockRows 3396)),(7126,some (fanBlockRows 3397)),(7127,some (fanBlockRows 3398)),(7128,some (fanBlockRows 3399)),(7129,some (fanBlockRows 3400)),(7130,some (fanBlockRows 3401)),(7131,some (fanBlockRows 3402)),(7132,some (fanBlockRows 3403)),(7133,some (fanBlockRows 3404)),(7134,some (fanBlockRows 3405)),(7135,some (fanBlockRows 3406)),(7136,some (fanBlockRows 3407)),(7137,some (fanBlockRows 3408)),(7138,some (fanBlockRows 3409)),(7139,some (fanBlockRows 3410)),(7140,some (fanBlockRows 3411)),(7141,some (fanBlockRows 3412)),(7142,some (fanBlockRows 3413)),(7143,some (fanBlockRows 3414)),(7144,some (fanBlockRows 3415)),(7145,some (fanBlockRows 3416)),(7146,some (fanBlockRows 3417)),(7147,some (fanBlockRows 3418)),(7148,some (fanBlockRows 3419)),(7149,some (fanBlockRows 3420)),(7150,some (fanBlockRows 3421)),(7151,some (fanBlockRows 3422)),(7152,some (fanBlockRows 3423)),(7153,some (fanBlockRows 3424)),(7154,none),(7155,none),(7156,none),(7157,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step05.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain6_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step05.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step05.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain6_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain6_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step05

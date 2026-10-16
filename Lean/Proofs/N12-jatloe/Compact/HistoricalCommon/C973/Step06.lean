import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step06
import Compact.HistoricalCommon.C973.Step06Groups00
import Compact.HistoricalCommon.C973.Step06Groups01
import Compact.HistoricalCommon.C973.Step06Groups02
import Compact.HistoricalCommon.C973.Step06Groups03
import Compact.HistoricalCommon.C973.Step06Groups04
import Compact.HistoricalCommon.C973.Step06Groups05
import Compact.HistoricalCommon.C973.Step06Groups06
import Compact.HistoricalCommon.C973.Step06Groups07

namespace N12Compact.HistoricalCommon.C973.Step06
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
  (.sourceCut 16 (.neighborCut 8 (.sourceCut 8 .leaf .leaf) (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 8 (.neighborCut 8 .leaf .leaf) .leaf))))) (.sourceCut 16 (.neighborCut 8 (.sourceCut 8 .leaf .leaf) (.neighborCut 8 (.sourceCut 8 (.neighborCut 4 .leaf .leaf) (.sourceCut 4 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))) (.neighborCut 8 (.sourceCut 8 .leaf (.sourceCut 8 (.neighborCut 4 .leaf .leaf) (.neighborCut 4 .leaf .leaf))) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.sourceCut 16 (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf)) .leaf))))))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8379_header,context8464_header,context8475_header,context8486_header,context8497_header,context8508_header,context8513_header,context8514_header,context8515_header,context8516_header,context8454_header,context8455_header,context8456_header,context8457_header,context8458_header,context8459_header,context8460_header,context8461_header,context8462_header,context8463_header,context8465_header,context8466_header,context8467_header,context8468_header,context8469_header,context8470_header,context8471_header,context8472_header,context8473_header,context8474_header,context8476_header,context8477_header,context8478_header,context8479_header,context8480_header,context8481_header,context8482_header,context8483_header,context8484_header,context8485_header,context8487_header,context8488_header,context8489_header,context8490_header,context8491_header,context8492_header,context8493_header,context8494_header,context8495_header,context8496_header,context8498_header,context8499_header,context8500_header,context8501_header,context8502_header,context8503_header,context8504_header,context8505_header,context8506_header,context8507_header,context8509_header,context8510_header,context8511_header,context8512_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7158,some (fanBlockRows 3428)),(7159,some (fanBlockRows 3439)),(7160,some (fanBlockRows 3450)),(7161,some (fanBlockRows 3461)),(7162,some (fanBlockRows 3472)),(7163,some (fanBlockRows 3483)),(7164,some (fanBlockRows 3488)),(7165,some (fanBlockRows 3489)),(7166,some (fanBlockRows 3490)),(7167,some (fanBlockRows 3491)),(7168,some (fanBlockRows 3429)),(7169,some (fanBlockRows 3430)),(7170,some (fanBlockRows 3431)),(7171,some (fanBlockRows 3432)),(7172,some (fanBlockRows 3433)),(7173,some (fanBlockRows 3434)),(7174,some (fanBlockRows 3435)),(7175,some (fanBlockRows 3436)),(7176,some (fanBlockRows 3437)),(7177,some (fanBlockRows 3438)),(7178,some (fanBlockRows 3440)),(7179,some (fanBlockRows 3441)),(7180,some (fanBlockRows 3442)),(7181,some (fanBlockRows 3443)),(7182,some (fanBlockRows 3444)),(7183,some (fanBlockRows 3445)),(7184,some (fanBlockRows 3446)),(7185,some (fanBlockRows 3447)),(7186,some (fanBlockRows 3448)),(7187,some (fanBlockRows 3449)),(7188,some (fanBlockRows 3451)),(7189,some (fanBlockRows 3452)),(7190,some (fanBlockRows 3453)),(7191,some (fanBlockRows 3454)),(7192,some (fanBlockRows 3455)),(7193,some (fanBlockRows 3456)),(7194,some (fanBlockRows 3457)),(7195,some (fanBlockRows 3458)),(7196,some (fanBlockRows 3459)),(7197,some (fanBlockRows 3460)),(7198,some (fanBlockRows 3462)),(7199,some (fanBlockRows 3463)),(7200,some (fanBlockRows 3464)),(7201,some (fanBlockRows 3465)),(7202,some (fanBlockRows 3466)),(7203,some (fanBlockRows 3467)),(7204,some (fanBlockRows 3468)),(7205,some (fanBlockRows 3469)),(7206,some (fanBlockRows 3470)),(7207,some (fanBlockRows 3471)),(7208,some (fanBlockRows 3473)),(7209,some (fanBlockRows 3474)),(7210,some (fanBlockRows 3475)),(7211,some (fanBlockRows 3476)),(7212,some (fanBlockRows 3477)),(7213,some (fanBlockRows 3478)),(7214,some (fanBlockRows 3479)),(7215,some (fanBlockRows 3480)),(7216,some (fanBlockRows 3481)),(7217,some (fanBlockRows 3482)),(7218,some (fanBlockRows 3484)),(7219,some (fanBlockRows 3485)),(7220,some (fanBlockRows 3486)),(7221,some (fanBlockRows 3487))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step06.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain8_2Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step06.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step06.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain8_2Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain8_2Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step06

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step04
import Compact.HistoricalCommon.C973.Step04Groups00
import Compact.HistoricalCommon.C973.Step04Groups01
import Compact.HistoricalCommon.C973.Step04Groups02
import Compact.HistoricalCommon.C973.Step04Groups03
import Compact.HistoricalCommon.C973.Step04Groups04
import Compact.HistoricalCommon.C973.Step04Groups05
import Compact.HistoricalCommon.C973.Step04Groups06
import Compact.HistoricalCommon.C973.Step04Groups07
import Compact.HistoricalCommon.C973.Step04Groups08
import Compact.HistoricalCommon.C973.Step04Groups09
import Compact.HistoricalCommon.C973.Step04Groups10

namespace N12Compact.HistoricalCommon.C973.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 8 .leaf .leaf))) (.neighborCut 16 .leaf (.sourceCut 4 (.neighborCut 16 .leaf .leaf) (.sourceCut 4 (.neighborCut 16 .leaf .leaf) (.sourceCut 8 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 16 .leaf (.sourceCut 8 (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf))))))))) (.sourceCut 16 (.neighborCut 16 (.sourceCut 8 (.neighborCut 8 .leaf (.sourceCut 4 .leaf .leaf)) .leaf) (.neighborCut 16 (.sourceCut 8 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 (.sourceCut 8 .leaf .leaf) (.neighborCut 8 (.sourceCut 4 .leaf (.sourceCut 4 .leaf .leaf)) .leaf)))) (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 8 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 (.sourceCut 4 .leaf (.sourceCut 4 .leaf (.sourceCut 4 .leaf .leaf))) .leaf)))))

theorem partition_checked : partition.Check ⟨0,64,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8199_header,context8273_header,context8284_header,context8295_header,context8306_header,context8317_header,context8322_header,context8323_header,context8324_header,context8325_header,context8263_header,context8264_header,context8265_header,context8266_header,context8267_header,context8268_header,context8269_header,context8270_header,context8271_header,context8272_header,context8274_header,context8275_header,context8276_header,context8277_header,context8278_header,context8279_header,context8280_header,context8281_header,context8282_header,context8283_header,context8285_header,context8286_header,context8287_header,context8288_header,context8289_header,context8290_header,context8291_header,context8292_header,context8293_header,context8294_header,context8296_header,context8297_header,context8298_header,context8299_header,context8300_header,context8301_header,context8302_header,context8303_header,context8304_header,context8305_header,context8307_header,context8308_header,context8309_header,context8310_header,context8311_header,context8312_header,context8313_header,context8314_header,context8315_header,context8316_header,context8318_header,context8319_header,context8320_header,context8321_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7030,some (fanBlockRows 3311)),(7031,some (fanBlockRows 3322)),(7032,some (fanBlockRows 3333)),(7033,some (fanBlockRows 3344)),(7034,some (fanBlockRows 3355)),(7035,some (fanBlockRows 3366)),(7036,some (fanBlockRows 3371)),(7037,some (fanBlockRows 3372)),(7038,some (fanBlockRows 3373)),(7039,some (fanBlockRows 3374)),(7040,some (fanBlockRows 3312)),(7041,some (fanBlockRows 3313)),(7042,some (fanBlockRows 3314)),(7043,some (fanBlockRows 3315)),(7044,some (fanBlockRows 3316)),(7045,some (fanBlockRows 3317)),(7046,some (fanBlockRows 3318)),(7047,some (fanBlockRows 3319)),(7048,some (fanBlockRows 3320)),(7049,some (fanBlockRows 3321)),(7050,some (fanBlockRows 3323)),(7051,some (fanBlockRows 3324)),(7052,some (fanBlockRows 3325)),(7053,some (fanBlockRows 3326)),(7054,some (fanBlockRows 3327)),(7055,some (fanBlockRows 3328)),(7056,some (fanBlockRows 3329)),(7057,some (fanBlockRows 3330)),(7058,some (fanBlockRows 3331)),(7059,some (fanBlockRows 3332)),(7060,some (fanBlockRows 3334)),(7061,some (fanBlockRows 3335)),(7062,some (fanBlockRows 3336)),(7063,some (fanBlockRows 3337)),(7064,some (fanBlockRows 3338)),(7065,some (fanBlockRows 3339)),(7066,some (fanBlockRows 3340)),(7067,some (fanBlockRows 3341)),(7068,some (fanBlockRows 3342)),(7069,some (fanBlockRows 3343)),(7070,some (fanBlockRows 3345)),(7071,some (fanBlockRows 3346)),(7072,some (fanBlockRows 3347)),(7073,some (fanBlockRows 3348)),(7074,some (fanBlockRows 3349)),(7075,some (fanBlockRows 3350)),(7076,some (fanBlockRows 3351)),(7077,some (fanBlockRows 3352)),(7078,some (fanBlockRows 3353)),(7079,some (fanBlockRows 3354)),(7080,some (fanBlockRows 3356)),(7081,some (fanBlockRows 3357)),(7082,some (fanBlockRows 3358)),(7083,some (fanBlockRows 3359)),(7084,some (fanBlockRows 3360)),(7085,some (fanBlockRows 3361)),(7086,some (fanBlockRows 3362)),(7087,some (fanBlockRows 3363)),(7088,some (fanBlockRows 3364)),(7089,some (fanBlockRows 3365)),(7090,some (fanBlockRows 3367)),(7091,some (fanBlockRows 3368)),(7092,some (fanBlockRows 3369)),(7093,some (fanBlockRows 3370))]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step04.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain5_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step04.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step04.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain5_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain5_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step04

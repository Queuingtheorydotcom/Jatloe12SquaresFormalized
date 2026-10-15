import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step08
import Compact.HistoricalCommon.C973.Step08Groups00
import Compact.HistoricalCommon.C973.Step08Groups01
import Compact.HistoricalCommon.C973.Step08Groups02
import Compact.HistoricalCommon.C973.Step08Groups03
import Compact.HistoricalCommon.C973.Step08Groups04
import Compact.HistoricalCommon.C973.Step08Groups05
import Compact.HistoricalCommon.C973.Step08Groups06

namespace N12Compact.HistoricalCommon.C973.Step08
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 23 (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 11 .leaf (.sourceCut 6 .leaf .leaf)) (.neighborCut 8 (.sourceCut 11 .leaf (.sourceCut 6 .leaf (.sourceCut 3 .leaf .leaf))) (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf)))))))))) (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,47,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 47) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 47) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8645_header,context8646_header,context8647_header,context8648_header,context8649_header,context8402_header,context8404_header,context8406_header,context8408_header,context8410_header,context8412_header,context8414_header,context8416_header,context8418_header,context8420_header,context8650_header,context8651_header,context8652_header,context8653_header,context8654_header,context8655_header,context8656_header,context8657_header,context8658_header,context8659_header,context8660_header,context8661_header,context8662_header,context8663_header,context8664_header,context8665_header,context8666_header,context8667_header,context8668_header,context8669_header,context8670_header,context8671_header,context8672_header,context8673_header,context8674_header,context8675_header,context8676_header,context8677_header,context8678_header,context8679_header,context8680_header,context8681_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 47).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(7586,none),(7587,none),(7588,none),(7589,none),(7590,none),(7591,none),(7592,none),(7593,none),(7594,none),(7595,none),(7596,none),(7597,none),(7598,none),(7599,none),(7600,none),(7601,none),(7602,some (fanBlockRows 3540)),(7603,some (fanBlockRows 3541)),(7604,some (fanBlockRows 3542)),(7605,some (fanBlockRows 3543)),(7606,some (fanBlockRows 3544)),(7607,some (fanBlockRows 59)),(7608,some (fanBlockRows 59)),(7609,some (fanBlockRows 59)),(7610,some (fanBlockRows 59)),(7611,some (fanBlockRows 59)),(7612,some (fanBlockRows 59)),(7613,some (fanBlockRows 59)),(7614,some (fanBlockRows 59)),(7615,some (fanBlockRows 59)),(7616,some (fanBlockRows 59)),(7617,some (fanBlockRows 3545)),(7618,some (fanBlockRows 3546)),(7619,some (fanBlockRows 3547)),(7620,some (fanBlockRows 3548)),(7621,some (fanBlockRows 3549)),(7622,some (fanBlockRows 3550)),(7623,some (fanBlockRows 3551)),(7624,some (fanBlockRows 3552)),(7625,some (fanBlockRows 3553)),(7626,some (fanBlockRows 3554)),(7627,some (fanBlockRows 3555)),(7628,some (fanBlockRows 3556)),(7629,some (fanBlockRows 3557)),(7630,some (fanBlockRows 3558)),(7631,some (fanBlockRows 3559)),(7632,some (fanBlockRows 3560)),(7633,some (fanBlockRows 3561)),(7634,some (fanBlockRows 3562)),(7635,some (fanBlockRows 3563)),(7636,some (fanBlockRows 3564)),(7637,some (fanBlockRows 3565)),(7638,some (fanBlockRows 3566)),(7639,some (fanBlockRows 3567)),(7640,some (fanBlockRows 3568)),(7641,some (fanBlockRows 3569)),(7642,some (fanBlockRows 3570)),(7643,some (fanBlockRows 3571)),(7644,some (fanBlockRows 3572)),(7645,some (fanBlockRows 3573)),(7646,some (fanBlockRows 3574)),(7647,some (fanBlockRows 3575)),(7648,some (fanBlockRows 3576)),(7649,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step08.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain7_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step08.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step08.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain7_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain7_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step08

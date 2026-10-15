import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step01
import Compact.HistoricalCommon.C701.Step01Groups00
import Compact.HistoricalCommon.C701.Step01Groups01
import Compact.HistoricalCommon.C701.Step01Groups02
import Compact.HistoricalCommon.C701.Step01Groups03
import Compact.HistoricalCommon.C701.Step01Groups04
import Compact.HistoricalCommon.C701.Step01Groups05
import Compact.HistoricalCommon.C701.Step01Groups06

namespace N12Compact.HistoricalCommon.C701.Step01
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 16 (.sourceCut 15 .leaf (.sourceCut 15 (.neighborCut 8 (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf)) .leaf) (.sourceCut 15 (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf)) (.sourceCut 8 (.neighborCut 8 .leaf (.sourceCut 4 .leaf .leaf)) .leaf)))) (.neighborCut 16 (.sourceCut 30 .leaf (.neighborCut 8 (.sourceCut 15 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))) .leaf)) (.neighborCut 16 .leaf (.sourceCut 30 .leaf (.neighborCut 8 .leaf (.sourceCut 15 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))))))))

theorem partition_checked : partition.Check ⟨0,61,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 61) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 61) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context8738_header,context8749_header,context8758_header,context8769_header,context8780_header,context8795_header,context8796_header,context8739_header,context8740_header,context8741_header,context8742_header,context8743_header,context8744_header,context8745_header,context8746_header,context8747_header,context8748_header,context8750_header,context8751_header,context8752_header,context8753_header,context8754_header,context8755_header,context8756_header,context8757_header,context7324_header,context7325_header,context8759_header,context8760_header,context8761_header,context8762_header,context8763_header,context8764_header,context8765_header,context8766_header,context8767_header,context8768_header,context8770_header,context8771_header,context8772_header,context8773_header,context8774_header,context8775_header,context8776_header,context8777_header,context8778_header,context8779_header,context8781_header,context8782_header,context8783_header,context8784_header,context8785_header,context8786_header,context8787_header,context8788_header,context8789_header,context8790_header,context8791_header,context8792_header,context8793_header,context8794_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 61).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(513,some (fanBlockRows 3628)),(514,some (fanBlockRows 3639)),(515,some (fanBlockRows 3648)),(516,some (fanBlockRows 3659)),(517,some (fanBlockRows 3670)),(518,none),(519,none),(520,none),(521,some (fanBlockRows 3685)),(522,some (fanBlockRows 3686)),(523,some (fanBlockRows 3629)),(524,some (fanBlockRows 3630)),(525,some (fanBlockRows 3631)),(526,some (fanBlockRows 3632)),(527,some (fanBlockRows 3633)),(528,some (fanBlockRows 3634)),(529,some (fanBlockRows 3635)),(530,some (fanBlockRows 3636)),(531,some (fanBlockRows 3637)),(532,some (fanBlockRows 3638)),(533,some (fanBlockRows 3640)),(534,some (fanBlockRows 3641)),(535,some (fanBlockRows 3642)),(536,some (fanBlockRows 3643)),(537,some (fanBlockRows 3644)),(538,some (fanBlockRows 3645)),(539,some (fanBlockRows 3646)),(540,some (fanBlockRows 3647)),(541,some (fanBlockRows 2945)),(542,some (fanBlockRows 2946)),(543,some (fanBlockRows 3649)),(544,some (fanBlockRows 3650)),(545,some (fanBlockRows 3651)),(546,some (fanBlockRows 3652)),(547,some (fanBlockRows 3653)),(548,some (fanBlockRows 3654)),(549,some (fanBlockRows 3655)),(550,some (fanBlockRows 3656)),(551,some (fanBlockRows 3657)),(552,some (fanBlockRows 3658)),(553,some (fanBlockRows 3660)),(554,some (fanBlockRows 3661)),(555,some (fanBlockRows 3662)),(556,some (fanBlockRows 3663)),(557,some (fanBlockRows 3664)),(558,some (fanBlockRows 3665)),(559,some (fanBlockRows 3666)),(560,some (fanBlockRows 3667)),(561,some (fanBlockRows 3668)),(562,some (fanBlockRows 3669)),(563,some (fanBlockRows 3671)),(564,some (fanBlockRows 3672)),(565,some (fanBlockRows 3673)),(566,some (fanBlockRows 3674)),(567,some (fanBlockRows 3675)),(568,some (fanBlockRows 3676)),(569,some (fanBlockRows 3677)),(570,some (fanBlockRows 3678)),(571,some (fanBlockRows 3679)),(572,some (fanBlockRows 3680)),(573,some (fanBlockRows 3681)),(574,some (fanBlockRows 3682)),(575,some (fanBlockRows 3683)),(576,some (fanBlockRows 3684))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step01.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain0_1Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step01.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step01.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain0_1Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain0_1Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step01

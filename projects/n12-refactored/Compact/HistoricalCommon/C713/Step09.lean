import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step09
import Compact.HistoricalCommon.C713.Step09Groups00
import Compact.HistoricalCommon.C713.Step09Groups01

namespace N12Compact.HistoricalCommon.C713.Step09
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 4 .leaf (.neighborCut 7 .leaf .leaf)))))

theorem partition_checked : partition.Check ⟨0,104,0,29⟩ scopes := by decide +kernel

theorem covered (i : Fin 104) (j : Fin 29) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 104) (j : Fin 29) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context3539_header,context3583_header,context3594_header,context3605_header,context3616_header,context3627_header,context3638_header,context3649_header,context3660_header,context3671_header,context3573_header,context3574_header,context3575_header,context3576_header,context3577_header,context3578_header,context3579_header,context3580_header,context3581_header,context3582_header,context3584_header,context3585_header,context3586_header,context3587_header,context3588_header,context3589_header,context3590_header,context3591_header,context3592_header,context3593_header,context3595_header,context3596_header,context3597_header,context3598_header,context3599_header,context3600_header,context3601_header,context3602_header,context3603_header,context3604_header,context3606_header,context3607_header,context3608_header,context3609_header,context3610_header,context3611_header,context3612_header,context3613_header,context3614_header,context3615_header,context3617_header,context3618_header,context3619_header,context3620_header,context3621_header,context3622_header,context3623_header,context3624_header,context3625_header,context3626_header,context3628_header,context3629_header,context3630_header,context3631_header,context3632_header,context3633_header,context3634_header,context3635_header,context3636_header,context3637_header,context3639_header,context3640_header,context3641_header,context3642_header,context3643_header,context3644_header,context3645_header,context3646_header,context3647_header,context3648_header,context3650_header,context3651_header,context3652_header,context3653_header,context3654_header,context3655_header,context3656_header,context3657_header,context3658_header,context3659_header,context3661_header,context3662_header,context3663_header,context3664_header,context3665_header,context3666_header,context3667_header,context3668_header,context3669_header,context3670_header,context3569_header,context3570_header,context3571_header,context3572_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 104).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3642,some (fanBlockRows 59)),(3643,some (fanBlockRows 59)),(3644,some (fanBlockRows 59)),(3645,some (fanBlockRows 59)),(3646,some (fanBlockRows 59)),(3647,some (fanBlockRows 59)),(3648,some (fanBlockRows 59)),(3649,some (fanBlockRows 59)),(3650,some (fanBlockRows 59)),(3651,some (fanBlockRows 59)),(3652,some (fanBlockRows 59)),(3653,some (fanBlockRows 59)),(3654,some (fanBlockRows 59)),(3655,some (fanBlockRows 59)),(3656,some (fanBlockRows 59)),(3657,some (fanBlockRows 59)),(3658,some (fanBlockRows 59)),(3659,some (fanBlockRows 59)),(3660,some (fanBlockRows 59)),(3661,some (fanBlockRows 59)),(3662,some (fanBlockRows 59)),(3663,some (fanBlockRows 59)),(3664,some (fanBlockRows 59)),(3665,some (fanBlockRows 59)),(3666,some (fanBlockRows 59)),(3667,some (fanBlockRows 59)),(3668,some (fanBlockRows 59)),(3669,some (fanBlockRows 59)),(3670,some (fanBlockRows 59)),(3671,some (fanBlockRows 59)),(3672,some (fanBlockRows 59)),(3673,some (fanBlockRows 59)),(3674,some (fanBlockRows 59)),(3675,some (fanBlockRows 59)),(3676,some (fanBlockRows 59)),(3677,some (fanBlockRows 59)),(3678,some (fanBlockRows 59)),(3679,some (fanBlockRows 59)),(3680,some (fanBlockRows 59)),(3681,some (fanBlockRows 59)),(3682,some (fanBlockRows 59)),(3683,some (fanBlockRows 59)),(3684,some (fanBlockRows 59)),(3685,some (fanBlockRows 59)),(3686,some (fanBlockRows 59)),(3687,some (fanBlockRows 59)),(3688,some (fanBlockRows 59)),(3689,some (fanBlockRows 59)),(3690,some (fanBlockRows 59)),(3691,some (fanBlockRows 59)),(3692,some (fanBlockRows 59)),(3693,some (fanBlockRows 59)),(3694,some (fanBlockRows 59)),(3695,some (fanBlockRows 59)),(3696,some (fanBlockRows 59)),(3697,some (fanBlockRows 59)),(3698,some (fanBlockRows 59)),(3699,some (fanBlockRows 59)),(3700,some (fanBlockRows 59)),(3701,some (fanBlockRows 59)),(3702,some (fanBlockRows 59)),(3703,some (fanBlockRows 59)),(3704,some (fanBlockRows 59)),(3705,some (fanBlockRows 59)),(3706,some (fanBlockRows 59)),(3707,some (fanBlockRows 59)),(3708,some (fanBlockRows 59)),(3709,some (fanBlockRows 59)),(3710,some (fanBlockRows 59)),(3711,some (fanBlockRows 59)),(3712,some (fanBlockRows 59)),(3713,some (fanBlockRows 59)),(3714,some (fanBlockRows 59)),(3715,some (fanBlockRows 59)),(3716,some (fanBlockRows 59)),(3717,some (fanBlockRows 59)),(3718,some (fanBlockRows 59)),(3719,some (fanBlockRows 59)),(3720,some (fanBlockRows 59)),(3721,some (fanBlockRows 59)),(3722,some (fanBlockRows 59)),(3723,some (fanBlockRows 59)),(3724,some (fanBlockRows 59)),(3725,some (fanBlockRows 59)),(3726,some (fanBlockRows 59)),(3727,some (fanBlockRows 59)),(3728,some (fanBlockRows 59)),(3729,some (fanBlockRows 59)),(3730,some (fanBlockRows 59)),(3731,some (fanBlockRows 59)),(3732,some (fanBlockRows 59)),(3733,some (fanBlockRows 59)),(3734,some (fanBlockRows 59)),(3735,some (fanBlockRows 59)),(3736,some (fanBlockRows 59)),(3737,some (fanBlockRows 59)),(3738,some (fanBlockRows 59)),(3739,some (fanBlockRows 59)),(3740,some (fanBlockRows 59)),(3741,some (fanBlockRows 59)),(3742,some (fanBlockRows 59)),(3743,some (fanBlockRows 59)),(3744,some (fanBlockRows 59)),(3745,some (fanBlockRows 59))]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step09.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 29).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain7_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step09.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step09.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain7_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain7_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step09

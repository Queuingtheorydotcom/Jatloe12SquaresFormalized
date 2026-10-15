import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step16
import Compact.HistoricalCommon.C979.Step16Groups00
import Compact.HistoricalCommon.C979.Step16Groups01
import Compact.HistoricalCommon.C979.Step16Groups02
import Compact.HistoricalCommon.C979.Step16Groups03
import Compact.HistoricalCommon.C979.Step16Groups04

namespace N12Compact.HistoricalCommon.C979.Step16
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 28 (.neighborCut 15 (.sourceCut 14 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 7 .leaf (.neighborCut 8 .leaf (.neighborCut 15 .leaf (.neighborCut 16 .leaf .leaf))))) (.sourceCut 29 (.neighborCut 61 .leaf .leaf) (.neighborCut 30 (.sourceCut 28 .leaf (.sourceCut 14 .leaf (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf)))) (.neighborCut 15 .leaf (.neighborCut 16 .leaf .leaf)))))

theorem partition_checked : partition.Check ⟨0,114,0,123⟩ scopes := by decide +kernel

theorem covered (i : Fin 114) (j : Fin 123) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 114) (j : Fin 123) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context10856_header,context10881_header,context10884_header,context10885_header,context10886_header,context10887_header,context10891_header,context10899_header,context10910_header,context10921_header,context10867_header,context10872_header,context10873_header,context10874_header,context10875_header,context10876_header,context10877_header,context10878_header,context10879_header,context10880_header,context10882_header,context10883_header,context1816_header,context1818_header,context1820_header,context1822_header,context1824_header,context1826_header,context1828_header,context1830_header,context1832_header,context1834_header,context1836_header,context1838_header,context1840_header,context1842_header,context1844_header,context1846_header,context1848_header,context1850_header,context1852_header,context1854_header,context1856_header,context1858_header,context1860_header,context1862_header,context1864_header,context1866_header,context1868_header,context1870_header,context1872_header,context1874_header,context1876_header,context1878_header,context1880_header,context1882_header,context1884_header,context1886_header,context1888_header,context1890_header,context1892_header,context10888_header,context10889_header,context10890_header,context1897_header,context1899_header,context1901_header,context1903_header,context1905_header,context1907_header,context1909_header,context1911_header,context1913_header,context10892_header,context10893_header,context10894_header,context10895_header,context10896_header,context10897_header,context10898_header,context10900_header,context10901_header,context10902_header,context10903_header,context10904_header,context10905_header,context10906_header,context10907_header,context10908_header,context10909_header,context10911_header,context10912_header,context10913_header,context10914_header,context10915_header,context10916_header,context10917_header,context10918_header,context10919_header,context10920_header,context10857_header,context10858_header,context10859_header,context10860_header,context10861_header,context10862_header,context10863_header,context10864_header,context10865_header,context10866_header,context10868_header,context10869_header,context10870_header,context10871_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 114).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3746,some (fanBlockRows 4559)),(3747,some (fanBlockRows 4584)),(3748,some (fanBlockRows 4587)),(3749,some (fanBlockRows 4588)),(3750,some (fanBlockRows 4589)),(3751,some (fanBlockRows 4590)),(3752,some (fanBlockRows 4594)),(3753,some (fanBlockRows 4602)),(3754,some (fanBlockRows 4613)),(3755,some (fanBlockRows 4624)),(3756,some (fanBlockRows 4570)),(3757,some (fanBlockRows 4575)),(3758,some (fanBlockRows 4576)),(3759,some (fanBlockRows 4577)),(3760,some (fanBlockRows 4578)),(3761,some (fanBlockRows 4579)),(3762,some (fanBlockRows 4580)),(3763,some (fanBlockRows 4581)),(3764,some (fanBlockRows 4582)),(3765,some (fanBlockRows 4583)),(3766,some (fanBlockRows 4585)),(3767,some (fanBlockRows 4586)),(3768,some (fanBlockRows 59)),(3769,some (fanBlockRows 59)),(3770,some (fanBlockRows 59)),(3771,some (fanBlockRows 59)),(3772,some (fanBlockRows 59)),(3773,some (fanBlockRows 59)),(3774,some (fanBlockRows 59)),(3775,some (fanBlockRows 59)),(3776,some (fanBlockRows 59)),(3777,some (fanBlockRows 59)),(3778,some (fanBlockRows 59)),(3779,some (fanBlockRows 59)),(3780,some (fanBlockRows 59)),(3781,some (fanBlockRows 59)),(3782,some (fanBlockRows 59)),(3783,some (fanBlockRows 59)),(3784,some (fanBlockRows 59)),(3785,some (fanBlockRows 59)),(3786,some (fanBlockRows 59)),(3787,some (fanBlockRows 59)),(3788,some (fanBlockRows 59)),(3789,some (fanBlockRows 59)),(3790,some (fanBlockRows 59)),(3791,some (fanBlockRows 59)),(3792,some (fanBlockRows 59)),(3793,some (fanBlockRows 59)),(3794,some (fanBlockRows 59)),(3795,some (fanBlockRows 59)),(3796,some (fanBlockRows 59)),(3797,some (fanBlockRows 59)),(3798,some (fanBlockRows 59)),(3799,some (fanBlockRows 59)),(3800,some (fanBlockRows 59)),(3801,some (fanBlockRows 59)),(3802,some (fanBlockRows 59)),(3803,some (fanBlockRows 59)),(3804,some (fanBlockRows 59)),(3805,some (fanBlockRows 59)),(3806,some (fanBlockRows 59)),(3807,some (fanBlockRows 4591)),(3808,some (fanBlockRows 4592)),(3809,some (fanBlockRows 4593)),(3810,some (fanBlockRows 59)),(3811,some (fanBlockRows 59)),(3812,some (fanBlockRows 59)),(3813,some (fanBlockRows 59)),(3814,some (fanBlockRows 59)),(3815,some (fanBlockRows 59)),(3816,some (fanBlockRows 59)),(3817,some (fanBlockRows 59)),(3818,some (fanBlockRows 59)),(3819,some (fanBlockRows 4595)),(3820,some (fanBlockRows 4596)),(3821,some (fanBlockRows 4597)),(3822,some (fanBlockRows 4598)),(3823,some (fanBlockRows 4599)),(3824,some (fanBlockRows 4600)),(3825,some (fanBlockRows 4601)),(3826,some (fanBlockRows 4603)),(3827,some (fanBlockRows 4604)),(3828,some (fanBlockRows 4605)),(3829,some (fanBlockRows 4606)),(3830,some (fanBlockRows 4607)),(3831,some (fanBlockRows 4608)),(3832,some (fanBlockRows 4609)),(3833,some (fanBlockRows 4610)),(3834,some (fanBlockRows 4611)),(3835,some (fanBlockRows 4612)),(3836,some (fanBlockRows 4614)),(3837,some (fanBlockRows 4615)),(3838,some (fanBlockRows 4616)),(3839,some (fanBlockRows 4617)),(3840,some (fanBlockRows 4618)),(3841,some (fanBlockRows 4619)),(3842,some (fanBlockRows 4620)),(3843,some (fanBlockRows 4621)),(3844,some (fanBlockRows 4622)),(3845,some (fanBlockRows 4623)),(3846,some (fanBlockRows 4560)),(3847,some (fanBlockRows 4561)),(3848,some (fanBlockRows 4562)),(3849,some (fanBlockRows 4563)),(3850,some (fanBlockRows 4564)),(11961,some (fanBlockRows 4565)),(11962,some (fanBlockRows 4566)),(11963,some (fanBlockRows 4567)),(11964,some (fanBlockRows 4568)),(11965,some (fanBlockRows 4569)),(11966,some (fanBlockRows 4571)),(11967,some (fanBlockRows 4572)),(11968,some (fanBlockRows 4573)),(11969,some (fanBlockRows 4574))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step16.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 123).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain6_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step16.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step16.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain6_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain6_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step16

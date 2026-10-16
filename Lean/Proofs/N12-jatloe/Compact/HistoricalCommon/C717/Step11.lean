import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step11
import Compact.HistoricalCommon.C717.Step11Groups00
import Compact.HistoricalCommon.C717.Step11Groups01
import Compact.HistoricalCommon.C717.Step11Groups02
import Compact.HistoricalCommon.C717.Step11Groups03
import Compact.HistoricalCommon.C717.Step11Groups04
import Compact.HistoricalCommon.C717.Step11Groups05
import Compact.HistoricalCommon.C717.Step11Groups06
import Compact.HistoricalCommon.C717.Step11Groups07

namespace N12Compact.HistoricalCommon.C717.Step11
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 49 (.neighborCut 11 (.sourceCut 12 .leaf (.sourceCut 12 .leaf .leaf)) (.neighborCut 12 (.sourceCut 6 .leaf (.sourceCut 6 .leaf (.sourceCut 12 (.neighborCut 6 .leaf .leaf) .leaf))) (.neighborCut 24 .leaf (.sourceCut 24 (.neighborCut 11 .leaf (.neighborCut 12 .leaf .leaf)) (.neighborCut 11 .leaf (.neighborCut 12 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) .leaf)))))) (.neighborCut 5 (.sourceCut 24 .leaf (.neighborCut 2 .leaf .leaf)) (.neighborCut 6 .leaf (.neighborCut 12 .leaf (.neighborCut 24 .leaf (.sourceCut 24 (.neighborCut 11 .leaf (.neighborCut 12 (.sourceCut 12 .leaf (.sourceCut 6 .leaf .leaf)) .leaf)) (.neighborCut 23 .leaf (.sourceCut 12 .leaf (.neighborCut 12 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,98,0,94⟩ scopes := by decide +kernel

theorem covered (i : Fin 98) (j : Fin 94) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 98) (j : Fin 94) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context4027_header,context4038_header,context4048_header,context4050_header,context4061_header,context4066_header,context4074_header,context4085_header,context4096_header,context4017_header,context4018_header,context4019_header,context4020_header,context4021_header,context4022_header,context4023_header,context4024_header,context4025_header,context4026_header,context4028_header,context4029_header,context4030_header,context4031_header,context4032_header,context4033_header,context4034_header,context4035_header,context4036_header,context4037_header,context4039_header,context4040_header,context4041_header,context4042_header,context4043_header,context4044_header,context4045_header,context4046_header,context4047_header,context1850_header,context1852_header,context1854_header,context1856_header,context1858_header,context1860_header,context1862_header,context1864_header,context1866_header,context1868_header,context4049_header,context4051_header,context4052_header,context4053_header,context4054_header,context4055_header,context4056_header,context4057_header,context4058_header,context4059_header,context4060_header,context4062_header,context4063_header,context4064_header,context4065_header,context4067_header,context4068_header,context4069_header,context4070_header,context4071_header,context4072_header,context4073_header,context4075_header,context4076_header,context4077_header,context4078_header,context4079_header,context4080_header,context4081_header,context4082_header,context4083_header,context4084_header,context4086_header,context4087_header,context4088_header,context4089_header,context4090_header,context4091_header,context4092_header,context4093_header,context4094_header,context4095_header,context3915_header,context4010_header,context4011_header,context4012_header,context4013_header,context4014_header,context4015_header,context4016_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 98).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3746,none),(3747,some (fanBlockRows 1492)),(3748,some (fanBlockRows 1503)),(3749,some (fanBlockRows 1513)),(3750,some (fanBlockRows 1515)),(3751,some (fanBlockRows 1526)),(3752,some (fanBlockRows 1531)),(3753,some (fanBlockRows 1539)),(3754,some (fanBlockRows 1550)),(3755,some (fanBlockRows 1561)),(3756,some (fanBlockRows 1482)),(3757,some (fanBlockRows 1483)),(3758,some (fanBlockRows 1484)),(3759,some (fanBlockRows 1485)),(3760,some (fanBlockRows 1486)),(3761,some (fanBlockRows 1487)),(3762,some (fanBlockRows 1488)),(3763,some (fanBlockRows 1489)),(3764,some (fanBlockRows 1490)),(3765,some (fanBlockRows 1491)),(3766,some (fanBlockRows 1493)),(3767,some (fanBlockRows 1494)),(3768,some (fanBlockRows 1495)),(3769,some (fanBlockRows 1496)),(3770,some (fanBlockRows 1497)),(3771,some (fanBlockRows 1498)),(3772,some (fanBlockRows 1499)),(3773,some (fanBlockRows 1500)),(3774,some (fanBlockRows 1501)),(3775,some (fanBlockRows 1502)),(3776,some (fanBlockRows 1504)),(3777,some (fanBlockRows 1505)),(3778,some (fanBlockRows 1506)),(3779,some (fanBlockRows 1507)),(3780,some (fanBlockRows 1508)),(3781,some (fanBlockRows 1509)),(3782,some (fanBlockRows 1510)),(3783,some (fanBlockRows 1511)),(3784,some (fanBlockRows 1512)),(3785,some (fanBlockRows 59)),(3786,some (fanBlockRows 59)),(3787,some (fanBlockRows 59)),(3788,some (fanBlockRows 59)),(3789,some (fanBlockRows 59)),(3790,some (fanBlockRows 59)),(3791,some (fanBlockRows 59)),(3792,some (fanBlockRows 59)),(3793,some (fanBlockRows 59)),(3794,some (fanBlockRows 59)),(3795,some (fanBlockRows 1514)),(3796,some (fanBlockRows 1516)),(3797,some (fanBlockRows 1517)),(3798,some (fanBlockRows 1518)),(3799,some (fanBlockRows 1519)),(3800,some (fanBlockRows 1520)),(3801,some (fanBlockRows 1521)),(3802,some (fanBlockRows 1522)),(3803,some (fanBlockRows 1523)),(3804,some (fanBlockRows 1524)),(3805,some (fanBlockRows 1525)),(3806,some (fanBlockRows 1527)),(3807,some (fanBlockRows 1528)),(3808,some (fanBlockRows 1529)),(3809,some (fanBlockRows 1530)),(3810,none),(3811,none),(3812,none),(3813,none),(3814,none),(3815,none),(3816,none),(3817,none),(3818,none),(3819,some (fanBlockRows 1532)),(3820,some (fanBlockRows 1533)),(3821,some (fanBlockRows 1534)),(3822,some (fanBlockRows 1535)),(3823,some (fanBlockRows 1536)),(3824,some (fanBlockRows 1537)),(3825,some (fanBlockRows 1538)),(3826,some (fanBlockRows 1540)),(3827,some (fanBlockRows 1541)),(3828,some (fanBlockRows 1542)),(3829,some (fanBlockRows 1543)),(3830,some (fanBlockRows 1544)),(3831,some (fanBlockRows 1545)),(3832,some (fanBlockRows 1546)),(3833,some (fanBlockRows 1547)),(3834,some (fanBlockRows 1548)),(3835,some (fanBlockRows 1549)),(3836,some (fanBlockRows 1551)),(3837,some (fanBlockRows 1552)),(3838,some (fanBlockRows 1553)),(3839,some (fanBlockRows 1554)),(3840,some (fanBlockRows 1555)),(3841,some (fanBlockRows 1556)),(3842,some (fanBlockRows 1557)),(3843,some (fanBlockRows 1558)),(3844,some (fanBlockRows 1559)),(3845,some (fanBlockRows 1560)),(3846,some (fanBlockRows 1474)),(3847,some (fanBlockRows 1475)),(3848,some (fanBlockRows 1476)),(3849,some (fanBlockRows 1477)),(3850,some (fanBlockRows 1478)),(3851,some (fanBlockRows 1479)),(3852,some (fanBlockRows 1480)),(3853,some (fanBlockRows 1481)),(3854,none),(3855,none),(3856,none),(3857,none),(3858,none),(3859,none)]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step11.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 94).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain2_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step11.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step11.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain2_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain2_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step11

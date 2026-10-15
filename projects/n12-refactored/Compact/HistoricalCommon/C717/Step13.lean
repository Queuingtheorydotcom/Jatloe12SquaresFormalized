import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step13
import Compact.HistoricalCommon.C717.Step13Groups00
import Compact.HistoricalCommon.C717.Step13Groups01
import Compact.HistoricalCommon.C717.Step13Groups02
import Compact.HistoricalCommon.C717.Step13Groups03
import Compact.HistoricalCommon.C717.Step13Groups04
import Compact.HistoricalCommon.C717.Step13Groups05
import Compact.HistoricalCommon.C717.Step13Groups06
import Compact.HistoricalCommon.C717.Step13Groups07
import Compact.HistoricalCommon.C717.Step13Groups08
import Compact.HistoricalCommon.C717.Step13Groups09
import Compact.HistoricalCommon.C717.Step13Groups10

namespace N12Compact.HistoricalCommon.C717.Step13
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 64 (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 16 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf))) (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))))))))) (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)))) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 32 .leaf .leaf) (.sourceCut 16 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 8 .leaf .leaf) .leaf)) (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 8 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,128,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context4228_header,context4395_header,context4406_header,context4417_header,context4428_header,context4439_header,context4450_header,context4463_header,context4484_header,context4498_header,context4367_header,context4378_header,context4387_header,context4388_header,context4389_header,context4390_header,context4391_header,context4392_header,context4393_header,context4394_header,context4396_header,context4397_header,context4398_header,context4399_header,context4400_header,context4401_header,context4402_header,context4403_header,context4404_header,context4405_header,context4407_header,context4408_header,context4409_header,context4410_header,context4411_header,context4412_header,context4413_header,context4414_header,context4415_header,context4416_header,context4418_header,context4419_header,context4420_header,context4421_header,context4422_header,context4423_header,context4424_header,context4425_header,context4426_header,context4427_header,context4429_header,context4430_header,context4431_header,context4432_header,context4433_header,context4434_header,context4435_header,context4436_header,context4437_header,context4438_header,context4440_header,context4441_header,context4442_header,context4443_header,context4444_header,context4445_header,context4446_header,context4447_header,context4448_header,context4449_header,context4451_header,context4452_header,context4453_header,context4454_header,context4455_header,context4456_header,context4457_header,context4458_header,context4460_header,context4462_header,context4465_header,context4467_header,context4469_header,context4471_header,context4473_header,context4475_header,context4477_header,context4479_header,context4481_header,context4483_header,context4486_header,context4488_header,context4490_header,context4491_header,context4492_header,context4493_header,context4494_header,context4495_header,context4496_header,context4497_header,context4357_header,context4358_header,context4359_header,context4360_header,context4361_header,context4362_header,context4363_header,context4364_header,context4365_header,context4366_header,context4368_header,context4369_header,context4370_header,context4371_header,context4372_header,context4373_header,context4374_header,context4375_header,context4376_header,context4377_header,context4379_header,context4380_header,context4381_header,context4382_header,context4383_header,context4384_header,context4385_header,context4386_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(2067,some (fanBlockRows 1583)),(3860,some (fanBlockRows 1622)),(3861,some (fanBlockRows 1633)),(3862,some (fanBlockRows 1644)),(3863,some (fanBlockRows 1655)),(3864,some (fanBlockRows 1666)),(3865,some (fanBlockRows 1677)),(3866,some (fanBlockRows 1686)),(3867,some (fanBlockRows 1687)),(3868,some (fanBlockRows 1695)),(3869,some (fanBlockRows 1594)),(3870,some (fanBlockRows 1605)),(3871,some (fanBlockRows 1614)),(3872,some (fanBlockRows 1615)),(3873,some (fanBlockRows 1616)),(3874,some (fanBlockRows 1617)),(3875,some (fanBlockRows 1618)),(3876,some (fanBlockRows 1619)),(3877,some (fanBlockRows 1620)),(3878,some (fanBlockRows 1621)),(3879,some (fanBlockRows 1623)),(3880,some (fanBlockRows 1624)),(3881,some (fanBlockRows 1625)),(3882,some (fanBlockRows 1626)),(3883,some (fanBlockRows 1627)),(3884,some (fanBlockRows 1628)),(3885,some (fanBlockRows 1629)),(3886,some (fanBlockRows 1630)),(3887,some (fanBlockRows 1631)),(3888,some (fanBlockRows 1632)),(3889,some (fanBlockRows 1634)),(3890,some (fanBlockRows 1635)),(3891,some (fanBlockRows 1636)),(3892,some (fanBlockRows 1637)),(3893,some (fanBlockRows 1638)),(3894,some (fanBlockRows 1639)),(3895,some (fanBlockRows 1640)),(3896,some (fanBlockRows 1641)),(3897,some (fanBlockRows 1642)),(3898,some (fanBlockRows 1643)),(3899,some (fanBlockRows 1645)),(3900,some (fanBlockRows 1646)),(3901,some (fanBlockRows 1647)),(3902,some (fanBlockRows 1648)),(3903,some (fanBlockRows 1649)),(3904,some (fanBlockRows 1650)),(3905,some (fanBlockRows 1651)),(3906,some (fanBlockRows 1652)),(3907,some (fanBlockRows 1653)),(3908,some (fanBlockRows 1654)),(3909,some (fanBlockRows 1656)),(3910,some (fanBlockRows 1657)),(3911,some (fanBlockRows 1658)),(3912,some (fanBlockRows 1659)),(3913,some (fanBlockRows 1660)),(3914,some (fanBlockRows 1661)),(3915,some (fanBlockRows 1662)),(3916,some (fanBlockRows 1663)),(3917,some (fanBlockRows 1664)),(3918,some (fanBlockRows 1665)),(3919,some (fanBlockRows 1667)),(3920,some (fanBlockRows 1668)),(3921,some (fanBlockRows 1669)),(3922,some (fanBlockRows 1670)),(3923,some (fanBlockRows 1671)),(3924,some (fanBlockRows 1672)),(3925,some (fanBlockRows 1673)),(3926,some (fanBlockRows 1674)),(3927,some (fanBlockRows 1675)),(3928,some (fanBlockRows 1676)),(3929,some (fanBlockRows 1678)),(3930,some (fanBlockRows 1679)),(3931,some (fanBlockRows 1680)),(3932,some (fanBlockRows 1681)),(3933,some (fanBlockRows 1682)),(3934,some (fanBlockRows 1683)),(3935,some (fanBlockRows 1684)),(3936,some (fanBlockRows 1685)),(3937,some (fanBlockRows 59)),(3938,some (fanBlockRows 59)),(3939,some (fanBlockRows 59)),(3940,some (fanBlockRows 59)),(3941,some (fanBlockRows 59)),(3942,some (fanBlockRows 59)),(3943,some (fanBlockRows 59)),(3944,some (fanBlockRows 59)),(3945,some (fanBlockRows 59)),(3946,some (fanBlockRows 59)),(3947,some (fanBlockRows 59)),(3948,some (fanBlockRows 59)),(3949,some (fanBlockRows 59)),(3950,some (fanBlockRows 59)),(3951,some (fanBlockRows 59)),(3952,some (fanBlockRows 1688)),(3953,some (fanBlockRows 1689)),(3954,some (fanBlockRows 1690)),(3955,some (fanBlockRows 1691)),(3956,some (fanBlockRows 1692)),(3957,some (fanBlockRows 1693)),(3958,some (fanBlockRows 1694)),(3959,some (fanBlockRows 1584)),(3960,some (fanBlockRows 1585)),(3961,some (fanBlockRows 1586)),(3962,some (fanBlockRows 1587)),(3963,some (fanBlockRows 1588)),(3964,some (fanBlockRows 1589)),(3965,some (fanBlockRows 1590)),(3966,some (fanBlockRows 1591)),(3967,some (fanBlockRows 1592)),(3968,some (fanBlockRows 1593)),(3969,some (fanBlockRows 1595)),(3970,some (fanBlockRows 1596)),(3971,some (fanBlockRows 1597)),(3972,some (fanBlockRows 1598)),(3973,some (fanBlockRows 1599)),(3974,some (fanBlockRows 1600)),(3975,some (fanBlockRows 1601)),(3976,some (fanBlockRows 1602)),(3977,some (fanBlockRows 1603)),(3978,some (fanBlockRows 1604)),(3979,some (fanBlockRows 1606)),(3980,some (fanBlockRows 1607)),(3981,some (fanBlockRows 1608)),(3982,some (fanBlockRows 1609)),(3983,some (fanBlockRows 1610)),(3984,some (fanBlockRows 1611)),(3985,some (fanBlockRows 1612)),(2194,some (fanBlockRows 1613))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step13.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain1_2Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step13.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step13.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain1_2Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain1_2Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step13

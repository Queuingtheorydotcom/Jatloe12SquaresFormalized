import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step14
import Compact.HistoricalCommon.C717.Step14Groups00
import Compact.HistoricalCommon.C717.Step14Groups01
import Compact.HistoricalCommon.C717.Step14Groups02
import Compact.HistoricalCommon.C717.Step14Groups03
import Compact.HistoricalCommon.C717.Step14Groups04
import Compact.HistoricalCommon.C717.Step14Groups05
import Compact.HistoricalCommon.C717.Step14Groups06

namespace N12Compact.HistoricalCommon.C717.Step14
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 6 (.neighborCut 5 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.sourceCut 3 .leaf .leaf)))) (.sourceCut 6 (.neighborCut 5 .leaf (.neighborCut 5 .leaf (.neighborCut 5 .leaf .leaf))) (.sourceCut 3 (.neighborCut 10 .leaf (.sourceCut 1 .leaf .leaf)) (.sourceCut 3 .leaf (.sourceCut 7 .leaf (.sourceCut 13 .leaf (.sourceCut 13 .leaf (.sourceCut 25 .leaf (.sourceCut 13 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 5 .leaf (.neighborCut 5 .leaf .leaf)))) (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 5 .leaf (.sourceCut 6 (.neighborCut 5 .leaf .leaf) .leaf)))))))))))))

theorem partition_checked : partition.Check ⟨0,102,0,21⟩ scopes := by decide +kernel

theorem covered (i : Fin 102) (j : Fin 21) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 102) (j : Fin 21) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context4533_header,context4544_header,context4555_header,context4566_header,context4577_header,context4588_header,context4599_header,context4610_header,context4621_header,context4522_header,context4524_header,context4525_header,context4526_header,context4527_header,context4528_header,context4529_header,context4530_header,context4531_header,context4532_header,context4534_header,context4535_header,context4536_header,context4537_header,context4538_header,context4539_header,context4540_header,context4541_header,context4542_header,context4543_header,context4545_header,context4546_header,context4547_header,context4548_header,context4549_header,context4550_header,context4551_header,context4552_header,context4553_header,context4554_header,context4556_header,context4557_header,context4558_header,context4559_header,context4560_header,context4561_header,context4562_header,context4563_header,context4564_header,context4565_header,context4567_header,context4568_header,context4569_header,context4570_header,context4571_header,context4572_header,context4573_header,context4574_header,context4575_header,context4576_header,context4578_header,context4579_header,context4580_header,context4581_header,context4582_header,context4583_header,context4584_header,context4585_header,context4586_header,context4587_header,context4589_header,context4590_header,context4591_header,context4592_header,context4593_header,context4594_header,context4595_header,context4596_header,context4597_header,context4598_header,context4600_header,context4601_header,context4602_header,context4603_header,context4604_header,context4605_header,context4606_header,context4607_header,context4608_header,context4609_header,context4611_header,context4612_header,context4613_header,context4614_header,context4615_header,context4616_header,context4617_header,context4618_header,context4619_header,context4620_header,context4499_header,context4521_header,context4523_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 102).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3986,none),(3987,some (fanBlockRows 1703)),(3988,some (fanBlockRows 1704)),(3989,some (fanBlockRows 1705)),(3990,some (fanBlockRows 1706)),(3991,some (fanBlockRows 1707)),(3992,some (fanBlockRows 1708)),(3993,some (fanBlockRows 1709)),(3994,some (fanBlockRows 1720)),(3995,some (fanBlockRows 1731)),(3996,some (fanBlockRows 1698)),(3997,some (fanBlockRows 1700)),(3998,some (fanBlockRows 1701)),(3999,some (fanBlockRows 1702)),(4000,some (fanBlockRows 59)),(4001,some (fanBlockRows 59)),(4002,some (fanBlockRows 59)),(4003,some (fanBlockRows 59)),(4004,some (fanBlockRows 59)),(4005,some (fanBlockRows 59)),(4006,some (fanBlockRows 59)),(4007,some (fanBlockRows 59)),(4008,some (fanBlockRows 59)),(4009,some (fanBlockRows 59)),(4010,some (fanBlockRows 59)),(4011,some (fanBlockRows 59)),(4012,some (fanBlockRows 59)),(4013,some (fanBlockRows 59)),(4014,some (fanBlockRows 59)),(4015,some (fanBlockRows 59)),(4016,some (fanBlockRows 59)),(4017,some (fanBlockRows 59)),(4018,some (fanBlockRows 59)),(4019,some (fanBlockRows 59)),(4020,some (fanBlockRows 59)),(4021,some (fanBlockRows 59)),(4022,some (fanBlockRows 59)),(4023,some (fanBlockRows 59)),(4024,some (fanBlockRows 59)),(4025,some (fanBlockRows 59)),(4026,some (fanBlockRows 59)),(4027,some (fanBlockRows 59)),(4028,some (fanBlockRows 59)),(4029,some (fanBlockRows 59)),(4030,some (fanBlockRows 59)),(4031,some (fanBlockRows 59)),(4032,some (fanBlockRows 59)),(4033,some (fanBlockRows 59)),(4034,some (fanBlockRows 59)),(4035,some (fanBlockRows 59)),(4036,some (fanBlockRows 59)),(4037,some (fanBlockRows 59)),(4038,some (fanBlockRows 59)),(4039,some (fanBlockRows 59)),(4040,some (fanBlockRows 59)),(4041,some (fanBlockRows 59)),(4042,some (fanBlockRows 59)),(4043,some (fanBlockRows 59)),(4044,some (fanBlockRows 59)),(4045,some (fanBlockRows 59)),(4046,some (fanBlockRows 59)),(4047,some (fanBlockRows 59)),(4048,some (fanBlockRows 59)),(4049,some (fanBlockRows 59)),(4050,some (fanBlockRows 59)),(4051,some (fanBlockRows 59)),(4052,some (fanBlockRows 59)),(4053,some (fanBlockRows 59)),(4054,some (fanBlockRows 59)),(4055,some (fanBlockRows 59)),(4056,some (fanBlockRows 59)),(4057,some (fanBlockRows 59)),(4058,some (fanBlockRows 59)),(4059,some (fanBlockRows 59)),(4060,some (fanBlockRows 59)),(4061,some (fanBlockRows 59)),(4062,some (fanBlockRows 59)),(4063,some (fanBlockRows 59)),(4064,some (fanBlockRows 59)),(4065,some (fanBlockRows 59)),(4066,some (fanBlockRows 1710)),(4067,some (fanBlockRows 1711)),(4068,some (fanBlockRows 1712)),(4069,some (fanBlockRows 1713)),(4070,some (fanBlockRows 1714)),(4071,some (fanBlockRows 1715)),(4072,some (fanBlockRows 1716)),(4073,some (fanBlockRows 1717)),(4074,some (fanBlockRows 1718)),(4075,some (fanBlockRows 1719)),(4076,some (fanBlockRows 1721)),(4077,some (fanBlockRows 1722)),(4078,some (fanBlockRows 1723)),(4079,some (fanBlockRows 1724)),(4080,some (fanBlockRows 1725)),(4081,some (fanBlockRows 1726)),(4082,some (fanBlockRows 1727)),(4083,some (fanBlockRows 1728)),(4084,some (fanBlockRows 1729)),(4085,some (fanBlockRows 1730)),(4086,some (fanBlockRows 1696)),(4087,some (fanBlockRows 1697)),(4088,none),(4089,none),(4090,none),(4091,none),(4092,none),(4093,none),(4094,none),(4095,none),(4096,none),(4097,none),(4098,some (fanBlockRows 1699))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step14.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 21).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain9_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step14.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step14.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain9_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain9_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step14

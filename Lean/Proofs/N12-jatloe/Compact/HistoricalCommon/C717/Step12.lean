import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step12
import Compact.HistoricalCommon.C717.Step12Groups00
import Compact.HistoricalCommon.C717.Step12Groups01
import Compact.HistoricalCommon.C717.Step12Groups02
import Compact.HistoricalCommon.C717.Step12Groups03
import Compact.HistoricalCommon.C717.Step12Groups04

namespace N12Compact.HistoricalCommon.C717.Step12
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
  (.sourceCut 6 (.neighborCut 13 .leaf (.neighborCut 7 .leaf .leaf)) (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 7 .leaf .leaf)) (.sourceCut 13 (.neighborCut 13 (.sourceCut 3 .leaf (.sourceCut 3 .leaf .leaf)) .leaf) (.sourceCut 26 .leaf (.sourceCut 26 .leaf (.sourceCut 13 .leaf (.sourceCut 6 .leaf (.neighborCut 13 .leaf (.neighborCut 3 .leaf (.neighborCut 4 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,104,0,27⟩ scopes := by decide +kernel

theorem covered (i : Fin 104) (j : Fin 27) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 104) (j : Fin 27) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context4097_header,context4139_header,context4150_header,context4161_header,context4172_header,context4183_header,context4194_header,context4205_header,context4216_header,context4227_header,context4129_header,context4130_header,context4131_header,context4132_header,context4133_header,context4134_header,context4135_header,context4136_header,context4137_header,context4138_header,context4140_header,context4141_header,context4142_header,context4143_header,context4144_header,context4145_header,context4146_header,context4147_header,context4148_header,context4149_header,context4151_header,context4152_header,context4153_header,context4154_header,context4155_header,context4156_header,context4157_header,context4158_header,context4159_header,context4160_header,context4162_header,context4163_header,context4164_header,context4165_header,context4166_header,context4167_header,context4168_header,context4169_header,context4170_header,context4171_header,context4173_header,context4174_header,context4175_header,context4176_header,context4177_header,context4178_header,context4179_header,context4180_header,context4181_header,context4182_header,context4184_header,context4185_header,context4186_header,context4187_header,context4188_header,context4189_header,context4190_header,context4191_header,context4192_header,context4193_header,context4195_header,context4196_header,context4197_header,context4198_header,context4199_header,context4200_header,context4201_header,context4202_header,context4203_header,context4204_header,context4206_header,context4207_header,context4208_header,context4209_header,context4210_header,context4211_header,context4212_header,context4213_header,context4214_header,context4215_header,context4217_header,context4218_header,context4219_header,context4220_header,context4221_header,context4222_header,context4223_header,context4224_header,context4225_header,context4226_header,context4125_header,context4126_header,context4127_header,context4128_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 104).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5785,some (fanBlockRows 1562)),(5786,some (fanBlockRows 1573)),(5787,some (fanBlockRows 1574)),(5788,some (fanBlockRows 1575)),(5789,some (fanBlockRows 1576)),(5790,some (fanBlockRows 1577)),(5791,some (fanBlockRows 1578)),(5792,some (fanBlockRows 1579)),(5793,some (fanBlockRows 1580)),(5794,some (fanBlockRows 1582)),(5795,some (fanBlockRows 1567)),(5796,some (fanBlockRows 1568)),(5797,some (fanBlockRows 1569)),(5798,some (fanBlockRows 1570)),(5799,some (fanBlockRows 1571)),(5800,some (fanBlockRows 1572)),(5801,some (fanBlockRows 59)),(5802,some (fanBlockRows 59)),(5803,some (fanBlockRows 59)),(5804,some (fanBlockRows 59)),(5805,some (fanBlockRows 59)),(5806,some (fanBlockRows 59)),(5807,some (fanBlockRows 59)),(5808,some (fanBlockRows 59)),(5809,some (fanBlockRows 59)),(5810,some (fanBlockRows 59)),(5811,some (fanBlockRows 59)),(5812,some (fanBlockRows 59)),(5813,some (fanBlockRows 59)),(5814,some (fanBlockRows 59)),(5815,some (fanBlockRows 59)),(5816,some (fanBlockRows 59)),(5817,some (fanBlockRows 59)),(5818,some (fanBlockRows 59)),(5819,some (fanBlockRows 59)),(5820,some (fanBlockRows 59)),(5821,some (fanBlockRows 59)),(5822,some (fanBlockRows 59)),(5823,some (fanBlockRows 59)),(5824,some (fanBlockRows 59)),(5825,some (fanBlockRows 59)),(5826,some (fanBlockRows 59)),(5827,some (fanBlockRows 59)),(5828,some (fanBlockRows 59)),(5829,some (fanBlockRows 59)),(5830,some (fanBlockRows 59)),(5831,some (fanBlockRows 59)),(5832,some (fanBlockRows 59)),(5833,some (fanBlockRows 59)),(5834,some (fanBlockRows 59)),(5835,some (fanBlockRows 59)),(5836,some (fanBlockRows 59)),(5837,some (fanBlockRows 59)),(5838,some (fanBlockRows 59)),(5839,some (fanBlockRows 59)),(5840,some (fanBlockRows 59)),(5841,some (fanBlockRows 59)),(5842,some (fanBlockRows 59)),(5843,some (fanBlockRows 59)),(5844,some (fanBlockRows 59)),(5845,some (fanBlockRows 59)),(5846,some (fanBlockRows 59)),(5847,some (fanBlockRows 59)),(5848,some (fanBlockRows 59)),(5849,some (fanBlockRows 59)),(5850,some (fanBlockRows 59)),(5851,some (fanBlockRows 59)),(5852,some (fanBlockRows 59)),(5853,some (fanBlockRows 59)),(5854,some (fanBlockRows 59)),(5855,some (fanBlockRows 59)),(5856,some (fanBlockRows 59)),(5857,some (fanBlockRows 59)),(5858,some (fanBlockRows 59)),(5859,some (fanBlockRows 59)),(5860,some (fanBlockRows 59)),(5861,some (fanBlockRows 59)),(5862,some (fanBlockRows 59)),(5863,some (fanBlockRows 59)),(5864,some (fanBlockRows 59)),(5865,some (fanBlockRows 59)),(5866,some (fanBlockRows 59)),(5867,some (fanBlockRows 59)),(5868,some (fanBlockRows 59)),(5869,some (fanBlockRows 59)),(5870,some (fanBlockRows 59)),(5871,some (fanBlockRows 59)),(5872,some (fanBlockRows 59)),(5873,some (fanBlockRows 59)),(5874,some (fanBlockRows 59)),(5875,some (fanBlockRows 59)),(5876,some (fanBlockRows 59)),(5877,some (fanBlockRows 59)),(5878,some (fanBlockRows 59)),(5879,some (fanBlockRows 59)),(5880,some (fanBlockRows 59)),(5881,some (fanBlockRows 59)),(5882,some (fanBlockRows 59)),(5883,some (fanBlockRows 59)),(5884,some (fanBlockRows 1581)),(5885,some (fanBlockRows 1563)),(5886,some (fanBlockRows 1564)),(5887,some (fanBlockRows 1565)),(5888,some (fanBlockRows 1566))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step12.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 27).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain6_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step12.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step12.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain6_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain6_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step12

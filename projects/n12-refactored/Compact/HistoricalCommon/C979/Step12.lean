import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step12
import Compact.HistoricalCommon.C979.Step12Groups00
import Compact.HistoricalCommon.C979.Step12Groups01
import Compact.HistoricalCommon.C979.Step12Groups02
import Compact.HistoricalCommon.C979.Step12Groups03
import Compact.HistoricalCommon.C979.Step12Groups04
import Compact.HistoricalCommon.C979.Step12Groups05
import Compact.HistoricalCommon.C979.Step12Groups06
import Compact.HistoricalCommon.C979.Step12Groups07
import Compact.HistoricalCommon.C979.Step12Groups08
import Compact.HistoricalCommon.C979.Step12Groups09

namespace N12Compact.HistoricalCommon.C979.Step12
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 62 (.neighborCut 14 (.sourceCut 31 .leaf (.sourceCut 15 .leaf (.neighborCut 7 .leaf .leaf))) (.neighborCut 14 (.sourceCut 31 .leaf .leaf) (.neighborCut 29 .leaf (.sourceCut 31 (.neighborCut 28 .leaf (.sourceCut 15 (.neighborCut 14 .leaf (.neighborCut 7 .leaf .leaf)) .leaf)) (.neighborCut 14 .leaf (.neighborCut 14 (.sourceCut 15 .leaf (.sourceCut 8 .leaf .leaf)) .leaf)))))) (.neighborCut 28 (.sourceCut 31 (.neighborCut 7 .leaf (.neighborCut 7 .leaf .leaf)) .leaf) (.neighborCut 29 .leaf (.sourceCut 15 (.neighborCut 28 .leaf .leaf) (.sourceCut 16 (.neighborCut 14 .leaf (.neighborCut 14 .leaf (.sourceCut 8 .leaf .leaf))) (.sourceCut 16 (.neighborCut 14 .leaf (.neighborCut 14 (.sourceCut 8 .leaf .leaf) (.neighborCut 14 .leaf .leaf))) (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 8 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,125,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 125) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 125) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context10170_header,context10181_header,context10192_header,context10203_header,context10214_header,context10225_header,context10236_header,context10247_header,context10133_header,context10144_header,context10152_header,context10153_header,context10154_header,context10155_header,context10156_header,context10157_header,context10158_header,context10159_header,context10160_header,context10161_header,context10162_header,context10163_header,context10164_header,context10165_header,context10166_header,context10167_header,context10168_header,context10169_header,context10171_header,context10172_header,context10173_header,context10174_header,context10175_header,context10176_header,context10177_header,context10178_header,context10179_header,context10180_header,context10182_header,context10183_header,context10184_header,context10185_header,context10186_header,context10187_header,context10188_header,context10189_header,context10190_header,context10191_header,context10193_header,context10194_header,context10195_header,context10196_header,context10197_header,context10198_header,context10199_header,context10200_header,context10201_header,context10202_header,context10204_header,context10205_header,context10206_header,context10207_header,context10208_header,context10209_header,context10210_header,context10211_header,context10212_header,context10213_header,context10215_header,context10216_header,context10217_header,context10218_header,context10219_header,context10220_header,context10221_header,context10222_header,context10223_header,context10224_header,context10226_header,context10227_header,context10228_header,context10229_header,context10230_header,context10231_header,context10232_header,context10233_header,context10234_header,context10235_header,context10237_header,context10238_header,context10239_header,context10240_header,context10241_header,context10242_header,context10243_header,context10244_header,context10245_header,context10246_header,context10114_header,context10124_header,context10125_header,context10126_header,context10127_header,context10128_header,context10129_header,context10130_header,context10131_header,context10132_header,context10134_header,context10135_header,context10136_header,context10137_header,context10138_header,context10139_header,context10140_header,context10141_header,context10142_header,context10143_header,context10145_header,context10146_header,context10147_header,context10148_header,context10149_header,context10150_header,context10151_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 125).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(10993,none),(10994,none),(10995,some (fanBlockRows 4300)),(10996,some (fanBlockRows 4311)),(10997,some (fanBlockRows 4319)),(10998,some (fanBlockRows 4330)),(10999,some (fanBlockRows 4341)),(11000,some (fanBlockRows 4352)),(11001,some (fanBlockRows 4363)),(11002,some (fanBlockRows 4374)),(11003,some (fanBlockRows 4263)),(11004,some (fanBlockRows 4274)),(11005,some (fanBlockRows 4282)),(11006,some (fanBlockRows 4283)),(11007,some (fanBlockRows 4284)),(11008,some (fanBlockRows 4285)),(11009,some (fanBlockRows 4286)),(11010,some (fanBlockRows 4287)),(11011,some (fanBlockRows 4288)),(11012,some (fanBlockRows 4289)),(11013,some (fanBlockRows 4290)),(11014,some (fanBlockRows 4291)),(11015,some (fanBlockRows 4292)),(11016,some (fanBlockRows 4293)),(11017,some (fanBlockRows 4294)),(11018,some (fanBlockRows 4295)),(11019,some (fanBlockRows 4296)),(11020,some (fanBlockRows 4297)),(11021,some (fanBlockRows 4298)),(11022,some (fanBlockRows 4299)),(11023,some (fanBlockRows 4301)),(11024,some (fanBlockRows 4302)),(11025,some (fanBlockRows 4303)),(11026,some (fanBlockRows 4304)),(11027,some (fanBlockRows 4305)),(11028,some (fanBlockRows 4306)),(11029,some (fanBlockRows 4307)),(11030,some (fanBlockRows 4308)),(11031,some (fanBlockRows 4309)),(11032,some (fanBlockRows 4310)),(11033,some (fanBlockRows 4312)),(11034,some (fanBlockRows 4313)),(11035,some (fanBlockRows 4314)),(11036,some (fanBlockRows 4315)),(11037,some (fanBlockRows 4316)),(11038,some (fanBlockRows 4317)),(11039,some (fanBlockRows 4318)),(11040,some (fanBlockRows 59)),(11041,some (fanBlockRows 59)),(11042,some (fanBlockRows 59)),(11043,some (fanBlockRows 4320)),(11044,some (fanBlockRows 4321)),(11045,some (fanBlockRows 4322)),(11046,some (fanBlockRows 4323)),(11047,some (fanBlockRows 4324)),(11048,some (fanBlockRows 4325)),(11049,some (fanBlockRows 4326)),(11050,some (fanBlockRows 4327)),(11051,some (fanBlockRows 4328)),(11052,some (fanBlockRows 4329)),(11053,some (fanBlockRows 4331)),(11054,some (fanBlockRows 4332)),(11055,some (fanBlockRows 4333)),(11056,some (fanBlockRows 4334)),(11057,some (fanBlockRows 4335)),(11058,some (fanBlockRows 4336)),(11059,some (fanBlockRows 4337)),(11060,some (fanBlockRows 4338)),(11061,some (fanBlockRows 4339)),(11062,some (fanBlockRows 4340)),(11063,some (fanBlockRows 4342)),(11064,some (fanBlockRows 4343)),(11065,some (fanBlockRows 4344)),(11066,some (fanBlockRows 4345)),(11067,some (fanBlockRows 4346)),(11068,some (fanBlockRows 4347)),(11069,some (fanBlockRows 4348)),(11070,some (fanBlockRows 4349)),(11071,some (fanBlockRows 4350)),(11072,some (fanBlockRows 4351)),(11073,some (fanBlockRows 4353)),(11074,some (fanBlockRows 4354)),(11075,some (fanBlockRows 4355)),(11076,some (fanBlockRows 4356)),(11077,some (fanBlockRows 4357)),(11078,some (fanBlockRows 4358)),(11079,some (fanBlockRows 4359)),(11080,some (fanBlockRows 4360)),(11081,some (fanBlockRows 4361)),(11082,some (fanBlockRows 4362)),(11083,some (fanBlockRows 4364)),(11084,some (fanBlockRows 4365)),(11085,some (fanBlockRows 4366)),(11086,some (fanBlockRows 4367)),(11087,some (fanBlockRows 4368)),(11088,some (fanBlockRows 4369)),(11089,some (fanBlockRows 4370)),(11090,some (fanBlockRows 4371)),(11091,some (fanBlockRows 4372)),(11092,some (fanBlockRows 4373)),(11093,some (fanBlockRows 4255)),(11094,some (fanBlockRows 59)),(11095,some (fanBlockRows 59)),(11096,some (fanBlockRows 4256)),(11097,some (fanBlockRows 4257)),(11098,some (fanBlockRows 4258)),(11099,some (fanBlockRows 4259)),(11100,some (fanBlockRows 4260)),(11101,some (fanBlockRows 4261)),(11102,some (fanBlockRows 4262)),(11103,some (fanBlockRows 4264)),(11104,some (fanBlockRows 4265)),(11105,some (fanBlockRows 4266)),(11106,some (fanBlockRows 4267)),(11107,some (fanBlockRows 4268)),(11108,some (fanBlockRows 4269)),(11109,some (fanBlockRows 4270)),(11110,some (fanBlockRows 4271)),(11111,some (fanBlockRows 4272)),(11112,some (fanBlockRows 4273)),(11113,some (fanBlockRows 4275)),(11114,some (fanBlockRows 4276)),(11115,some (fanBlockRows 4277)),(11116,some (fanBlockRows 4278)),(11117,some (fanBlockRows 4279)),(11118,some (fanBlockRows 4280)),(11119,some (fanBlockRows 4281)),(11120,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step12.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step12.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step12.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step12

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step11
import Compact.HistoricalCommon.C979.Step11Groups00
import Compact.HistoricalCommon.C979.Step11Groups01
import Compact.HistoricalCommon.C979.Step11Groups02
import Compact.HistoricalCommon.C979.Step11Groups03
import Compact.HistoricalCommon.C979.Step11Groups04
import Compact.HistoricalCommon.C979.Step11Groups05
import Compact.HistoricalCommon.C979.Step11Groups06
import Compact.HistoricalCommon.C979.Step11Groups07
import Compact.HistoricalCommon.C979.Step11Groups08
import Compact.HistoricalCommon.C979.Step11Groups09
import Compact.HistoricalCommon.C979.Step11Groups10
import Compact.HistoricalCommon.C979.Step11Groups11
import Compact.HistoricalCommon.C979.Step11Groups12
import Compact.HistoricalCommon.C979.Step11Groups13

namespace N12Compact.HistoricalCommon.C979.Step11
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44,group45,group46,group47,group48,group49,group50,group51,group52,group53,group54,group55]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope,group45_scope,group46_scope,group47_scope,group48_scope,group49_scope,group50_scope,group51_scope,group52_scope,group53_scope,group54_scope,group55_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 28 (.neighborCut 11 (.sourceCut 14 .leaf .leaf) (.neighborCut 6 (.sourceCut 14 .leaf .leaf) (.neighborCut 6 (.sourceCut 14 .leaf .leaf) (.neighborCut 12 .leaf (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 5 .leaf (.neighborCut 6 .leaf (.neighborCut 12 .leaf .leaf)))))))))) (.sourceCut 28 (.neighborCut 23 (.sourceCut 14 (.neighborCut 11 .leaf .leaf) (.sourceCut 7 .leaf .leaf)) (.neighborCut 12 .leaf (.neighborCut 6 .leaf (.neighborCut 6 .leaf (.neighborCut 5 .leaf (.neighborCut 6 .leaf (.neighborCut 12 .leaf (.neighborCut 12 .leaf .leaf)))))))) (.sourceCut 28 (.neighborCut 23 (.sourceCut 14 .leaf (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf))) (.neighborCut 12 .leaf (.neighborCut 6 .leaf (.neighborCut 6 .leaf (.neighborCut 11 .leaf (.neighborCut 12 .leaf (.sourceCut 14 .leaf (.neighborCut 12 .leaf (.sourceCut 7 .leaf .leaf))))))))) (.neighborCut 11 (.sourceCut 14 .leaf .leaf) (.neighborCut 6 (.sourceCut 14 .leaf .leaf) (.neighborCut 6 (.sourceCut 14 .leaf .leaf) (.neighborCut 12 .leaf (.neighborCut 6 .leaf (.neighborCut 6 .leaf (.sourceCut 14 (.neighborCut 11 .leaf (.neighborCut 12 .leaf .leaf)) (.neighborCut 11 .leaf (.neighborCut 12 (.sourceCut 7 .leaf .leaf) (.neighborCut 12 .leaf .leaf)))))))))))))

theorem partition_checked : partition.Check ⟨0,112,0,94⟩ scopes := by decide +kernel

theorem covered (i : Fin 112) (j : Fin 94) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 112) (j : Fin 94) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9907_header,context10041_header,context10052_header,context10063_header,context10071_header,context10072_header,context10080_header,context10091_header,context10102_header,context10113_header,context10013_header,context10024_header,context10033_header,context10034_header,context10035_header,context10036_header,context10037_header,context10038_header,context10039_header,context10040_header,context10042_header,context10043_header,context10044_header,context10045_header,context10046_header,context10047_header,context10048_header,context10049_header,context10050_header,context10051_header,context10053_header,context10054_header,context10055_header,context10056_header,context10057_header,context10058_header,context10059_header,context10060_header,context10061_header,context10062_header,context10064_header,context10065_header,context10066_header,context10067_header,context10068_header,context10069_header,context10070_header,context10073_header,context10074_header,context10075_header,context10076_header,context10077_header,context10078_header,context10079_header,context10081_header,context10082_header,context10083_header,context10084_header,context10085_header,context10086_header,context10087_header,context10088_header,context10089_header,context10090_header,context10092_header,context10093_header,context10094_header,context10095_header,context10096_header,context10097_header,context10098_header,context10099_header,context10100_header,context10101_header,context10103_header,context10104_header,context10105_header,context10106_header,context10107_header,context10108_header,context10109_header,context10110_header,context10111_header,context10112_header,context10003_header,context10004_header,context10005_header,context10006_header,context10007_header,context10008_header,context10009_header,context10010_header,context10011_header,context10012_header,context10014_header,context10015_header,context10016_header,context10017_header,context10018_header,context10019_header,context10020_header,context10021_header,context10022_header,context10023_header,context10025_header,context10026_header,context10027_header,context10028_header,context10029_header,context10030_header,context10031_header,context10032_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 112).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(10865,some (fanBlockRows 4143)),(10866,some (fanBlockRows 4182)),(10867,some (fanBlockRows 4193)),(10868,some (fanBlockRows 4204)),(10869,some (fanBlockRows 4212)),(10870,some (fanBlockRows 4213)),(10871,some (fanBlockRows 4221)),(10872,some (fanBlockRows 4232)),(10873,some (fanBlockRows 4243)),(10874,some (fanBlockRows 4254)),(10875,some (fanBlockRows 4154)),(10876,some (fanBlockRows 4165)),(10877,some (fanBlockRows 4174)),(10878,some (fanBlockRows 4175)),(10879,some (fanBlockRows 4176)),(10880,some (fanBlockRows 4177)),(10881,some (fanBlockRows 4178)),(10882,some (fanBlockRows 4179)),(10883,some (fanBlockRows 4180)),(10884,some (fanBlockRows 4181)),(10885,some (fanBlockRows 4183)),(10886,some (fanBlockRows 4184)),(10887,some (fanBlockRows 4185)),(10888,some (fanBlockRows 4186)),(10889,some (fanBlockRows 4187)),(10890,some (fanBlockRows 4188)),(10891,some (fanBlockRows 4189)),(10892,some (fanBlockRows 4190)),(10893,some (fanBlockRows 4191)),(10894,some (fanBlockRows 4192)),(10895,some (fanBlockRows 4194)),(10896,some (fanBlockRows 4195)),(10897,some (fanBlockRows 4196)),(10898,some (fanBlockRows 4197)),(10899,some (fanBlockRows 4198)),(10900,some (fanBlockRows 4199)),(10901,some (fanBlockRows 4200)),(10902,some (fanBlockRows 4201)),(10903,some (fanBlockRows 4202)),(10904,some (fanBlockRows 4203)),(10905,some (fanBlockRows 4205)),(10906,some (fanBlockRows 4206)),(10907,some (fanBlockRows 4207)),(10908,some (fanBlockRows 4208)),(10909,some (fanBlockRows 4209)),(10910,some (fanBlockRows 4210)),(10911,some (fanBlockRows 4211)),(10912,none),(10913,none),(10914,none),(10915,none),(10916,none),(10917,none),(10918,none),(10919,none),(10920,none),(10921,none),(10922,none),(10923,none),(10924,none),(10925,none),(10926,none),(10927,none),(10928,some (fanBlockRows 4214)),(10929,some (fanBlockRows 4215)),(10930,some (fanBlockRows 4216)),(10931,some (fanBlockRows 4217)),(10932,some (fanBlockRows 4218)),(10933,some (fanBlockRows 4219)),(10934,some (fanBlockRows 4220)),(10935,some (fanBlockRows 4222)),(10936,some (fanBlockRows 4223)),(10937,some (fanBlockRows 4224)),(10938,some (fanBlockRows 4225)),(10939,some (fanBlockRows 4226)),(10940,some (fanBlockRows 4227)),(10941,some (fanBlockRows 4228)),(10942,some (fanBlockRows 4229)),(10943,some (fanBlockRows 4230)),(10944,some (fanBlockRows 4231)),(10945,some (fanBlockRows 4233)),(10946,some (fanBlockRows 4234)),(10947,some (fanBlockRows 4235)),(10948,some (fanBlockRows 4236)),(10949,some (fanBlockRows 4237)),(10950,some (fanBlockRows 4238)),(10951,some (fanBlockRows 4239)),(10952,some (fanBlockRows 4240)),(10953,some (fanBlockRows 4241)),(10954,some (fanBlockRows 4242)),(10955,some (fanBlockRows 4244)),(10956,some (fanBlockRows 4245)),(10957,some (fanBlockRows 4246)),(10958,some (fanBlockRows 4247)),(10959,some (fanBlockRows 4248)),(10960,some (fanBlockRows 4249)),(10961,some (fanBlockRows 4250)),(10962,some (fanBlockRows 4251)),(10963,some (fanBlockRows 4252)),(10964,some (fanBlockRows 4253)),(10965,some (fanBlockRows 4144)),(10966,some (fanBlockRows 4145)),(10967,some (fanBlockRows 4146)),(10968,some (fanBlockRows 4147)),(10969,some (fanBlockRows 4148)),(10970,some (fanBlockRows 4149)),(10971,some (fanBlockRows 4150)),(10972,some (fanBlockRows 4151)),(10973,some (fanBlockRows 4152)),(10974,some (fanBlockRows 4153)),(10975,some (fanBlockRows 4155)),(10976,some (fanBlockRows 4156)),(10977,some (fanBlockRows 4157)),(10978,some (fanBlockRows 4158)),(10979,some (fanBlockRows 4159)),(10980,some (fanBlockRows 4160)),(10981,some (fanBlockRows 4161)),(10982,some (fanBlockRows 4162)),(10983,some (fanBlockRows 4163)),(10984,some (fanBlockRows 4164)),(10985,some (fanBlockRows 4166)),(10986,some (fanBlockRows 4167)),(10987,some (fanBlockRows 4168)),(10988,some (fanBlockRows 4169)),(10989,some (fanBlockRows 4170)),(10990,some (fanBlockRows 4171)),(10991,some (fanBlockRows 4172)),(10992,some (fanBlockRows 4173))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step11.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 94).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain7_5Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step11.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step11.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain7_5Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain7_5Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step11

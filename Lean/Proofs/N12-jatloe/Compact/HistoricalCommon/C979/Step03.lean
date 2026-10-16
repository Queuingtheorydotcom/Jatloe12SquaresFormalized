import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step03
import Compact.HistoricalCommon.C979.Step03Groups00
import Compact.HistoricalCommon.C979.Step03Groups01
import Compact.HistoricalCommon.C979.Step03Groups02
import Compact.HistoricalCommon.C979.Step03Groups03
import Compact.HistoricalCommon.C979.Step03Groups04
import Compact.HistoricalCommon.C979.Step03Groups05
import Compact.HistoricalCommon.C979.Step03Groups06
import Compact.HistoricalCommon.C979.Step03Groups07
import Compact.HistoricalCommon.C979.Step03Groups08

namespace N12Compact.HistoricalCommon.C979.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 14 .leaf (.sourceCut 16 (.neighborCut 28 .leaf .leaf) (.sourceCut 8 (.neighborCut 28 .leaf .leaf) (.sourceCut 4 (.neighborCut 28 .leaf .leaf) (.neighborCut 28 .leaf .leaf))))))) (.sourceCut 32 (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 16 .leaf (.neighborCut 7 .leaf .leaf)) (.neighborCut 14 .leaf .leaf))) (.sourceCut 32 (.neighborCut 28 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf .leaf)))) (.neighborCut 28 (.sourceCut 16 (.neighborCut 14 .leaf .leaf) .leaf) (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 14 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.sourceCut 16 (.neighborCut 14 .leaf .leaf) .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,128,0,113⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 113) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 113) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context12109_header,context12148_header,context12159_header,context12170_header,context12181_header,context12192_header,context12203_header,context12214_header,context12225_header,context12236_header,context12120_header,context12131_header,context12140_header,context12141_header,context12142_header,context12143_header,context12144_header,context12145_header,context12146_header,context12147_header,context12149_header,context12150_header,context12151_header,context12152_header,context12153_header,context12154_header,context12155_header,context12156_header,context12157_header,context12158_header,context12160_header,context12161_header,context12162_header,context12163_header,context12164_header,context12165_header,context12166_header,context12167_header,context12168_header,context12169_header,context12171_header,context12172_header,context12173_header,context12174_header,context12175_header,context12176_header,context12177_header,context12178_header,context12179_header,context12180_header,context12182_header,context12183_header,context12184_header,context12185_header,context12186_header,context12187_header,context12188_header,context12189_header,context12190_header,context12191_header,context12193_header,context12194_header,context12195_header,context12196_header,context12197_header,context12198_header,context12199_header,context12200_header,context12201_header,context12202_header,context12204_header,context12205_header,context12206_header,context12207_header,context12208_header,context12209_header,context12210_header,context12211_header,context12212_header,context12213_header,context12215_header,context12216_header,context12217_header,context12218_header,context12219_header,context12220_header,context12221_header,context12222_header,context12223_header,context12224_header,context12226_header,context12227_header,context12228_header,context12229_header,context12230_header,context12231_header,context12232_header,context12233_header,context12234_header,context12235_header,context12110_header,context12111_header,context12112_header,context12113_header,context12114_header,context12115_header,context12116_header,context12117_header,context12118_header,context12119_header,context12121_header,context12122_header,context12123_header,context12124_header,context12125_header,context12126_header,context12127_header,context12128_header,context12129_header,context12130_header,context12132_header,context12133_header,context12134_header,context12135_header,context12136_header,context12137_header,context12138_header,context12139_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(10084,some (fanBlockRows 5083)),(10085,some (fanBlockRows 5122)),(10086,some (fanBlockRows 5133)),(10087,some (fanBlockRows 5144)),(10088,some (fanBlockRows 5155)),(10089,some (fanBlockRows 5166)),(10090,some (fanBlockRows 5177)),(10091,some (fanBlockRows 5188)),(10092,some (fanBlockRows 5199)),(10093,some (fanBlockRows 5210)),(10094,some (fanBlockRows 5094)),(10095,some (fanBlockRows 5105)),(10096,some (fanBlockRows 5114)),(10097,some (fanBlockRows 5115)),(10098,some (fanBlockRows 5116)),(10099,some (fanBlockRows 5117)),(10100,some (fanBlockRows 5118)),(10101,some (fanBlockRows 5119)),(10102,some (fanBlockRows 5120)),(10103,some (fanBlockRows 5121)),(10104,some (fanBlockRows 5123)),(10105,some (fanBlockRows 5124)),(10106,some (fanBlockRows 5125)),(10107,some (fanBlockRows 5126)),(10108,some (fanBlockRows 5127)),(10109,some (fanBlockRows 5128)),(10110,some (fanBlockRows 5129)),(10111,some (fanBlockRows 5130)),(10112,some (fanBlockRows 5131)),(10113,some (fanBlockRows 5132)),(10114,some (fanBlockRows 5134)),(10115,some (fanBlockRows 5135)),(10116,some (fanBlockRows 5136)),(10117,some (fanBlockRows 5137)),(10118,some (fanBlockRows 5138)),(10119,some (fanBlockRows 5139)),(10120,some (fanBlockRows 5140)),(10121,some (fanBlockRows 5141)),(10122,some (fanBlockRows 5142)),(10123,some (fanBlockRows 5143)),(10124,some (fanBlockRows 5145)),(10125,some (fanBlockRows 5146)),(10126,some (fanBlockRows 5147)),(10127,some (fanBlockRows 5148)),(10128,some (fanBlockRows 5149)),(10129,some (fanBlockRows 5150)),(10130,some (fanBlockRows 5151)),(10131,some (fanBlockRows 5152)),(10132,some (fanBlockRows 5153)),(10133,some (fanBlockRows 5154)),(10134,some (fanBlockRows 5156)),(10135,some (fanBlockRows 5157)),(10136,some (fanBlockRows 5158)),(10137,some (fanBlockRows 5159)),(10138,some (fanBlockRows 5160)),(10139,some (fanBlockRows 5161)),(10140,some (fanBlockRows 5162)),(10141,some (fanBlockRows 5163)),(10142,some (fanBlockRows 5164)),(10143,some (fanBlockRows 5165)),(10144,some (fanBlockRows 5167)),(10145,some (fanBlockRows 5168)),(10146,some (fanBlockRows 5169)),(10147,some (fanBlockRows 5170)),(10148,some (fanBlockRows 5171)),(10149,some (fanBlockRows 5172)),(10150,some (fanBlockRows 5173)),(10151,some (fanBlockRows 5174)),(10152,some (fanBlockRows 5175)),(10153,some (fanBlockRows 5176)),(10154,some (fanBlockRows 5178)),(10155,some (fanBlockRows 5179)),(10156,some (fanBlockRows 5180)),(10157,some (fanBlockRows 5181)),(10158,some (fanBlockRows 5182)),(10159,some (fanBlockRows 5183)),(10160,some (fanBlockRows 5184)),(10161,some (fanBlockRows 5185)),(10162,some (fanBlockRows 5186)),(10163,some (fanBlockRows 5187)),(10164,some (fanBlockRows 5189)),(10165,some (fanBlockRows 5190)),(10166,some (fanBlockRows 5191)),(10167,some (fanBlockRows 5192)),(10168,some (fanBlockRows 5193)),(10169,some (fanBlockRows 5194)),(10170,some (fanBlockRows 5195)),(10171,some (fanBlockRows 5196)),(10172,some (fanBlockRows 5197)),(10173,some (fanBlockRows 5198)),(10174,some (fanBlockRows 5200)),(10175,some (fanBlockRows 5201)),(10176,some (fanBlockRows 5202)),(10177,some (fanBlockRows 5203)),(10178,some (fanBlockRows 5204)),(10179,some (fanBlockRows 5205)),(10180,some (fanBlockRows 5206)),(10181,some (fanBlockRows 5207)),(10182,some (fanBlockRows 5208)),(10183,some (fanBlockRows 5209)),(10184,some (fanBlockRows 5084)),(10185,some (fanBlockRows 5085)),(10186,some (fanBlockRows 5086)),(10187,some (fanBlockRows 5087)),(10188,some (fanBlockRows 5088)),(10189,some (fanBlockRows 5089)),(10190,some (fanBlockRows 5090)),(10191,some (fanBlockRows 5091)),(10192,some (fanBlockRows 5092)),(10193,some (fanBlockRows 5093)),(10194,some (fanBlockRows 5095)),(10195,some (fanBlockRows 5096)),(10196,some (fanBlockRows 5097)),(10197,some (fanBlockRows 5098)),(10198,some (fanBlockRows 5099)),(10199,some (fanBlockRows 5100)),(10200,some (fanBlockRows 5101)),(10201,some (fanBlockRows 5102)),(10202,some (fanBlockRows 5103)),(10203,some (fanBlockRows 5104)),(10204,some (fanBlockRows 5106)),(10205,some (fanBlockRows 5107)),(10206,some (fanBlockRows 5108)),(10207,some (fanBlockRows 5109)),(10208,some (fanBlockRows 5110)),(10209,some (fanBlockRows 5111)),(10210,some (fanBlockRows 5112)),(10211,some (fanBlockRows 5113))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step03.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 113).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain8_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step03.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step03.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain8_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain8_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step03

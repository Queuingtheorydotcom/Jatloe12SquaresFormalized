import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step06
import Compact.HistoricalCommon.C717.Step06Groups00
import Compact.HistoricalCommon.C717.Step06Groups01
import Compact.HistoricalCommon.C717.Step06Groups02
import Compact.HistoricalCommon.C717.Step06Groups03
import Compact.HistoricalCommon.C717.Step06Groups04
import Compact.HistoricalCommon.C717.Step06Groups05
import Compact.HistoricalCommon.C717.Step06Groups06
import Compact.HistoricalCommon.C717.Step06Groups07
import Compact.HistoricalCommon.C717.Step06Groups08
import Compact.HistoricalCommon.C717.Step06Groups09

namespace N12Compact.HistoricalCommon.C717.Step06
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 32 (.sourceCut 16 (.neighborCut 16 .leaf .leaf) .leaf) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf .leaf))))) (.sourceCut 32 (.neighborCut 32 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) (.neighborCut 32 (.sourceCut 16 (.neighborCut 16 .leaf .leaf) .leaf) (.neighborCut 32 (.sourceCut 16 .leaf .leaf) (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)) .leaf)))) (.sourceCut 32 (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 16 (.sourceCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf)))) (.neighborCut 64 (.sourceCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.neighborCut 16 .leaf .leaf)))) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 16 (.neighborCut 16 .leaf .leaf) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,128,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context5815_header,context5982_header,context5993_header,context6004_header,context6015_header,context6026_header,context6037_header,context6048_header,context6059_header,context6070_header,context5954_header,context5965_header,context5974_header,context5975_header,context5976_header,context5977_header,context5978_header,context5979_header,context5980_header,context5981_header,context5983_header,context5984_header,context5985_header,context5986_header,context5987_header,context5988_header,context5989_header,context5990_header,context5991_header,context5992_header,context5994_header,context5995_header,context5996_header,context5997_header,context5998_header,context5999_header,context6000_header,context6001_header,context6002_header,context6003_header,context6005_header,context6006_header,context6007_header,context6008_header,context6009_header,context6010_header,context6011_header,context6012_header,context6013_header,context6014_header,context6016_header,context6017_header,context6018_header,context6019_header,context6020_header,context6021_header,context6022_header,context6023_header,context6024_header,context6025_header,context6027_header,context6028_header,context6029_header,context6030_header,context6031_header,context6032_header,context6033_header,context6034_header,context6035_header,context6036_header,context6038_header,context6039_header,context6040_header,context6041_header,context6042_header,context6043_header,context6044_header,context6045_header,context6046_header,context6047_header,context6049_header,context6050_header,context6051_header,context6052_header,context6053_header,context6054_header,context6055_header,context6056_header,context6057_header,context6058_header,context6060_header,context6061_header,context6062_header,context6063_header,context6064_header,context6065_header,context6066_header,context6067_header,context6068_header,context6069_header,context5944_header,context5945_header,context5946_header,context5947_header,context5948_header,context5949_header,context5950_header,context5951_header,context5952_header,context5953_header,context5955_header,context5956_header,context5957_header,context5958_header,context5959_header,context5960_header,context5961_header,context5962_header,context5963_header,context5964_header,context5966_header,context5967_header,context5968_header,context5969_header,context5970_header,context5971_header,context5972_header,context5973_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5275,some (fanBlockRows 2324)),(5276,some (fanBlockRows 2349)),(5277,some (fanBlockRows 59)),(5278,some (fanBlockRows 59)),(5279,some (fanBlockRows 59)),(5280,some (fanBlockRows 59)),(5281,some (fanBlockRows 59)),(5282,some (fanBlockRows 59)),(5283,some (fanBlockRows 2379)),(5284,some (fanBlockRows 2390)),(5285,some (fanBlockRows 2335)),(5286,some (fanBlockRows 2338)),(5287,some (fanBlockRows 2341)),(5288,some (fanBlockRows 2342)),(5289,some (fanBlockRows 2343)),(5290,some (fanBlockRows 2344)),(5291,some (fanBlockRows 2345)),(5292,some (fanBlockRows 2346)),(5293,some (fanBlockRows 2347)),(5294,some (fanBlockRows 2348)),(5295,some (fanBlockRows 2350)),(5296,some (fanBlockRows 2351)),(5297,some (fanBlockRows 2352)),(5298,some (fanBlockRows 2353)),(5299,some (fanBlockRows 2354)),(5300,some (fanBlockRows 2355)),(5301,some (fanBlockRows 2356)),(5302,some (fanBlockRows 2357)),(5303,some (fanBlockRows 2358)),(5304,some (fanBlockRows 2359)),(5305,some (fanBlockRows 2360)),(5306,some (fanBlockRows 2361)),(5307,some (fanBlockRows 2362)),(5308,some (fanBlockRows 2363)),(5309,some (fanBlockRows 2364)),(5310,some (fanBlockRows 59)),(5311,some (fanBlockRows 59)),(5312,some (fanBlockRows 59)),(5313,some (fanBlockRows 59)),(5314,some (fanBlockRows 59)),(5315,some (fanBlockRows 59)),(5316,some (fanBlockRows 59)),(5317,some (fanBlockRows 59)),(5318,some (fanBlockRows 59)),(5319,some (fanBlockRows 59)),(5320,some (fanBlockRows 59)),(5321,some (fanBlockRows 59)),(5322,some (fanBlockRows 59)),(5323,some (fanBlockRows 59)),(5324,some (fanBlockRows 59)),(5325,some (fanBlockRows 59)),(5326,some (fanBlockRows 59)),(5327,some (fanBlockRows 59)),(5328,some (fanBlockRows 59)),(5329,some (fanBlockRows 59)),(5330,some (fanBlockRows 59)),(5331,some (fanBlockRows 59)),(5332,some (fanBlockRows 59)),(5333,some (fanBlockRows 59)),(5334,some (fanBlockRows 59)),(5335,some (fanBlockRows 59)),(5336,some (fanBlockRows 59)),(5337,some (fanBlockRows 59)),(5338,some (fanBlockRows 59)),(5339,some (fanBlockRows 59)),(5340,some (fanBlockRows 59)),(5341,some (fanBlockRows 59)),(5342,some (fanBlockRows 59)),(5343,some (fanBlockRows 59)),(5344,some (fanBlockRows 59)),(5345,some (fanBlockRows 59)),(5346,some (fanBlockRows 59)),(5347,some (fanBlockRows 59)),(5348,some (fanBlockRows 59)),(5349,some (fanBlockRows 59)),(5350,some (fanBlockRows 59)),(5351,some (fanBlockRows 2365)),(5352,some (fanBlockRows 2366)),(5353,some (fanBlockRows 2367)),(5354,some (fanBlockRows 2368)),(5355,some (fanBlockRows 2369)),(5356,some (fanBlockRows 2370)),(5357,some (fanBlockRows 2371)),(5358,some (fanBlockRows 2372)),(5359,some (fanBlockRows 2373)),(5360,some (fanBlockRows 2374)),(5361,some (fanBlockRows 2375)),(5362,some (fanBlockRows 2376)),(5363,some (fanBlockRows 2377)),(5364,some (fanBlockRows 2378)),(5365,some (fanBlockRows 2380)),(5366,some (fanBlockRows 2381)),(5367,some (fanBlockRows 2382)),(5368,some (fanBlockRows 2383)),(5369,some (fanBlockRows 2384)),(5370,some (fanBlockRows 2385)),(5371,some (fanBlockRows 2386)),(5372,some (fanBlockRows 2387)),(5373,some (fanBlockRows 2388)),(5374,some (fanBlockRows 2389)),(5375,some (fanBlockRows 2325)),(5376,some (fanBlockRows 2326)),(5377,some (fanBlockRows 2327)),(5378,some (fanBlockRows 2328)),(5379,some (fanBlockRows 2329)),(5380,some (fanBlockRows 2330)),(5381,some (fanBlockRows 2331)),(5382,some (fanBlockRows 2332)),(5383,some (fanBlockRows 2333)),(5384,some (fanBlockRows 2334)),(5385,some (fanBlockRows 2336)),(5386,some (fanBlockRows 2337)),(5387,some (fanBlockRows 59)),(5388,some (fanBlockRows 59)),(5389,some (fanBlockRows 59)),(5390,some (fanBlockRows 59)),(5391,some (fanBlockRows 59)),(5392,some (fanBlockRows 59)),(5393,some (fanBlockRows 59)),(5394,some (fanBlockRows 59)),(5395,some (fanBlockRows 59)),(5396,some (fanBlockRows 59)),(5397,some (fanBlockRows 59)),(5398,some (fanBlockRows 59)),(5399,some (fanBlockRows 59)),(5400,some (fanBlockRows 59)),(5401,some (fanBlockRows 2339)),(5402,some (fanBlockRows 2340))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step06.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain7_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step06.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step06.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain7_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain7_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step06

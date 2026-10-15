import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step08
import Compact.HistoricalCommon.C717.Step08Groups00
import Compact.HistoricalCommon.C717.Step08Groups01
import Compact.HistoricalCommon.C717.Step08Groups02
import Compact.HistoricalCommon.C717.Step08Groups03
import Compact.HistoricalCommon.C717.Step08Groups04
import Compact.HistoricalCommon.C717.Step08Groups05
import Compact.HistoricalCommon.C717.Step08Groups06
import Compact.HistoricalCommon.C717.Step08Groups07
import Compact.HistoricalCommon.C717.Step08Groups08

namespace N12Compact.HistoricalCommon.C717.Step08
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 49 (.neighborCut 16 (.sourceCut 24 .leaf .leaf) (.neighborCut 16 (.sourceCut 12 .leaf (.sourceCut 6 .leaf (.sourceCut 6 .leaf .leaf))) (.neighborCut 32 .leaf .leaf))) (.neighborCut 8 (.sourceCut 25 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.sourceCut 12 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 6 .leaf .leaf) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 6 .leaf .leaf))))) (.sourceCut 13 (.neighborCut 32 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))))) (.neighborCut 32 .leaf (.neighborCut 32 (.sourceCut 12 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf) (.neighborCut 16 (.sourceCut 12 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,99,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 99) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 99) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6266_header,context6277_header,context6288_header,context6299_header,context6305_header,context6311_header,context6322_header,context6331_header,context6342_header,context6254_header,context6257_header,context6258_header,context6259_header,context6260_header,context6261_header,context6262_header,context6263_header,context6264_header,context6265_header,context6267_header,context6268_header,context6269_header,context6270_header,context6271_header,context6272_header,context6273_header,context6274_header,context6275_header,context6276_header,context6278_header,context6279_header,context6280_header,context6281_header,context6282_header,context6283_header,context6284_header,context6285_header,context6286_header,context6287_header,context6289_header,context6290_header,context6291_header,context6292_header,context6293_header,context6294_header,context6295_header,context6296_header,context6297_header,context6298_header,context6300_header,context6301_header,context6302_header,context6303_header,context6304_header,context6306_header,context6307_header,context6308_header,context6309_header,context6310_header,context6312_header,context6313_header,context6314_header,context6315_header,context6316_header,context6317_header,context6318_header,context6319_header,context6320_header,context6321_header,context6323_header,context6324_header,context6325_header,context6326_header,context6327_header,context6328_header,context6329_header,context6330_header,context6332_header,context6333_header,context6334_header,context6335_header,context6336_header,context6337_header,context6338_header,context6339_header,context6340_header,context6341_header,context6131_header,context6245_header,context6246_header,context6247_header,context6248_header,context6249_header,context6250_header,context6251_header,context6252_header,context6253_header,context6255_header,context6256_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 99).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5497,none),(5498,some (fanBlockRows 2433)),(5499,some (fanBlockRows 2444)),(5500,some (fanBlockRows 2455)),(5501,some (fanBlockRows 2466)),(5502,some (fanBlockRows 2472)),(5503,some (fanBlockRows 2478)),(5504,some (fanBlockRows 2489)),(5505,some (fanBlockRows 2498)),(5506,some (fanBlockRows 2509)),(5507,some (fanBlockRows 2421)),(5508,some (fanBlockRows 2424)),(5509,some (fanBlockRows 2425)),(5510,some (fanBlockRows 2426)),(5511,some (fanBlockRows 2427)),(5512,some (fanBlockRows 2428)),(5513,some (fanBlockRows 2429)),(5514,some (fanBlockRows 2430)),(5515,some (fanBlockRows 2431)),(5516,some (fanBlockRows 2432)),(5517,some (fanBlockRows 2434)),(5518,some (fanBlockRows 2435)),(5519,some (fanBlockRows 2436)),(5520,some (fanBlockRows 2437)),(5521,some (fanBlockRows 2438)),(5522,some (fanBlockRows 2439)),(5523,some (fanBlockRows 2440)),(5524,some (fanBlockRows 2441)),(5525,some (fanBlockRows 2442)),(5526,some (fanBlockRows 2443)),(5527,some (fanBlockRows 2445)),(5528,some (fanBlockRows 2446)),(5529,some (fanBlockRows 2447)),(5530,some (fanBlockRows 2448)),(5531,some (fanBlockRows 2449)),(5532,some (fanBlockRows 2450)),(5533,some (fanBlockRows 2451)),(5534,some (fanBlockRows 2452)),(5535,some (fanBlockRows 2453)),(5536,some (fanBlockRows 2454)),(5537,some (fanBlockRows 2456)),(5538,some (fanBlockRows 2457)),(5539,some (fanBlockRows 2458)),(5540,some (fanBlockRows 2459)),(5541,some (fanBlockRows 2460)),(5542,some (fanBlockRows 2461)),(5543,some (fanBlockRows 2462)),(5544,some (fanBlockRows 2463)),(5545,some (fanBlockRows 2464)),(5546,some (fanBlockRows 2465)),(5547,some (fanBlockRows 2467)),(5548,some (fanBlockRows 2468)),(5549,some (fanBlockRows 2469)),(5550,some (fanBlockRows 2470)),(5551,some (fanBlockRows 2471)),(5552,none),(5553,none),(5554,none),(5555,none),(5556,none),(5557,none),(5558,none),(5559,none),(5560,none),(5561,none),(5562,some (fanBlockRows 2473)),(5563,some (fanBlockRows 2474)),(5564,some (fanBlockRows 2475)),(5565,some (fanBlockRows 2476)),(5566,some (fanBlockRows 2477)),(5567,some (fanBlockRows 2479)),(5568,some (fanBlockRows 2480)),(5569,some (fanBlockRows 2481)),(5570,some (fanBlockRows 2482)),(5571,some (fanBlockRows 2483)),(5572,some (fanBlockRows 2484)),(5573,some (fanBlockRows 2485)),(5574,some (fanBlockRows 2486)),(5575,some (fanBlockRows 2487)),(5576,some (fanBlockRows 2488)),(5577,some (fanBlockRows 2490)),(5578,some (fanBlockRows 2491)),(5579,none),(5580,none),(5581,some (fanBlockRows 2492)),(5582,some (fanBlockRows 2493)),(5583,some (fanBlockRows 2494)),(5584,some (fanBlockRows 2495)),(5585,some (fanBlockRows 2496)),(5586,some (fanBlockRows 2497)),(5587,some (fanBlockRows 2499)),(5588,some (fanBlockRows 2500)),(5589,some (fanBlockRows 2501)),(5590,some (fanBlockRows 2502)),(5591,some (fanBlockRows 2503)),(5592,some (fanBlockRows 2504)),(5593,some (fanBlockRows 2505)),(5594,some (fanBlockRows 2506)),(5595,some (fanBlockRows 2507)),(5596,some (fanBlockRows 2508)),(5597,some (fanBlockRows 2411)),(5598,some (fanBlockRows 2412)),(5599,some (fanBlockRows 2413)),(5600,some (fanBlockRows 2414)),(5601,some (fanBlockRows 2415)),(5602,some (fanBlockRows 2416)),(5603,some (fanBlockRows 2417)),(5604,some (fanBlockRows 2418)),(5605,some (fanBlockRows 2419)),(5606,some (fanBlockRows 2420)),(5607,some (fanBlockRows 2422)),(5608,some (fanBlockRows 2423)),(5609,none),(5610,none),(5611,none),(5612,none),(5613,none),(5614,none),(5615,none),(5616,none),(5617,none),(5618,none),(5619,none),(5620,none),(5621,none),(5622,none),(5623,none),(5624,none)]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step08.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain3_4Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step08.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step08.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain3_4Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain3_4Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step08

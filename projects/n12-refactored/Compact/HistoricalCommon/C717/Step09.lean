import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step09
import Compact.HistoricalCommon.C717.Step09Groups00
import Compact.HistoricalCommon.C717.Step09Groups01
import Compact.HistoricalCommon.C717.Step09Groups02
import Compact.HistoricalCommon.C717.Step09Groups03
import Compact.HistoricalCommon.C717.Step09Groups04
import Compact.HistoricalCommon.C717.Step09Groups05
import Compact.HistoricalCommon.C717.Step09Groups06
import Compact.HistoricalCommon.C717.Step09Groups07
import Compact.HistoricalCommon.C717.Step09Groups08
import Compact.HistoricalCommon.C717.Step09Groups09

namespace N12Compact.HistoricalCommon.C717.Step09
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
  (.sourceCut 16 (.neighborCut 6 (.sourceCut 8 .leaf .leaf) (.neighborCut 7 (.sourceCut 8 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 7 .leaf .leaf))) (.sourceCut 8 (.neighborCut 13 (.sourceCut 4 .leaf .leaf) (.neighborCut 7 .leaf .leaf)) (.sourceCut 8 .leaf (.sourceCut 32 (.neighborCut 13 (.sourceCut 8 .leaf (.sourceCut 8 .leaf .leaf)) .leaf) (.sourceCut 16 .leaf (.sourceCut 16 (.neighborCut 13 .leaf (.sourceCut 8 (.neighborCut 7 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 3 .leaf (.neighborCut 4 .leaf (.neighborCut 3 .leaf .leaf))))) (.sourceCut 16 (.neighborCut 13 .leaf (.sourceCut 8 (.neighborCut 7 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 7 .leaf (.neighborCut 3 .leaf .leaf)))) (.sourceCut 8 .leaf (.neighborCut 13 .leaf (.neighborCut 7 .leaf (.sourceCut 4 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,128,0,27⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 27) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 27) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6343_header,context6382_header,context6393_header,context6404_header,context6415_header,context6426_header,context6437_header,context6448_header,context6459_header,context6470_header,context6354_header,context6365_header,context6374_header,context6375_header,context6376_header,context6377_header,context6378_header,context6379_header,context6380_header,context6381_header,context6383_header,context6384_header,context6385_header,context6386_header,context6387_header,context6388_header,context6389_header,context6390_header,context6391_header,context6392_header,context6394_header,context6395_header,context6396_header,context6397_header,context6398_header,context6399_header,context6400_header,context6401_header,context6402_header,context6403_header,context6405_header,context6406_header,context6407_header,context6408_header,context6409_header,context6410_header,context6411_header,context6412_header,context6413_header,context6414_header,context6416_header,context6417_header,context6418_header,context6419_header,context6420_header,context6421_header,context6422_header,context6423_header,context6424_header,context6425_header,context6427_header,context6428_header,context6429_header,context6430_header,context6431_header,context6432_header,context6433_header,context6434_header,context6435_header,context6436_header,context6438_header,context6439_header,context6440_header,context6441_header,context6442_header,context6443_header,context6444_header,context6445_header,context6446_header,context6447_header,context6449_header,context6450_header,context6451_header,context6452_header,context6453_header,context6454_header,context6455_header,context6456_header,context6457_header,context6458_header,context6460_header,context6461_header,context6462_header,context6463_header,context6464_header,context6465_header,context6466_header,context6467_header,context6468_header,context6469_header,context6344_header,context6345_header,context6346_header,context6347_header,context6348_header,context6349_header,context6350_header,context6351_header,context6352_header,context6353_header,context6355_header,context6356_header,context6357_header,context6358_header,context6359_header,context6360_header,context6361_header,context6362_header,context6363_header,context6364_header,context6366_header,context6367_header,context6368_header,context6369_header,context6370_header,context6371_header,context6372_header,context6373_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(5654,some (fanBlockRows 2510)),(5655,some (fanBlockRows 2523)),(5656,some (fanBlockRows 59)),(5657,some (fanBlockRows 59)),(5658,some (fanBlockRows 59)),(5659,some (fanBlockRows 59)),(5660,some (fanBlockRows 59)),(5661,some (fanBlockRows 59)),(5662,some (fanBlockRows 59)),(5663,some (fanBlockRows 59)),(5664,some (fanBlockRows 2511)),(5665,some (fanBlockRows 2512)),(5666,some (fanBlockRows 2515)),(5667,some (fanBlockRows 2516)),(5668,some (fanBlockRows 2517)),(5669,some (fanBlockRows 2518)),(5670,some (fanBlockRows 2519)),(5671,some (fanBlockRows 2520)),(5672,some (fanBlockRows 2521)),(5673,some (fanBlockRows 2522)),(5674,some (fanBlockRows 2524)),(5675,some (fanBlockRows 2525)),(5676,some (fanBlockRows 2526)),(5677,some (fanBlockRows 2527)),(5678,some (fanBlockRows 59)),(5679,some (fanBlockRows 59)),(5680,some (fanBlockRows 59)),(5681,some (fanBlockRows 59)),(5682,some (fanBlockRows 59)),(5683,some (fanBlockRows 59)),(5684,some (fanBlockRows 59)),(5685,some (fanBlockRows 59)),(5686,some (fanBlockRows 59)),(5687,some (fanBlockRows 59)),(5688,some (fanBlockRows 59)),(5689,some (fanBlockRows 59)),(5690,some (fanBlockRows 59)),(5691,some (fanBlockRows 59)),(5692,some (fanBlockRows 59)),(5693,some (fanBlockRows 59)),(5694,some (fanBlockRows 59)),(5695,some (fanBlockRows 59)),(5696,some (fanBlockRows 59)),(5697,some (fanBlockRows 59)),(5698,some (fanBlockRows 59)),(5699,some (fanBlockRows 59)),(5700,some (fanBlockRows 59)),(5701,some (fanBlockRows 59)),(5702,some (fanBlockRows 59)),(5703,some (fanBlockRows 59)),(5704,some (fanBlockRows 59)),(5705,some (fanBlockRows 59)),(5706,some (fanBlockRows 59)),(5707,some (fanBlockRows 59)),(5708,some (fanBlockRows 59)),(5709,some (fanBlockRows 59)),(5710,some (fanBlockRows 59)),(5711,some (fanBlockRows 59)),(5712,some (fanBlockRows 59)),(5713,some (fanBlockRows 59)),(5714,some (fanBlockRows 59)),(5715,some (fanBlockRows 59)),(5716,some (fanBlockRows 59)),(5717,some (fanBlockRows 59)),(5718,some (fanBlockRows 59)),(5719,some (fanBlockRows 59)),(5720,some (fanBlockRows 59)),(5721,some (fanBlockRows 59)),(5722,some (fanBlockRows 59)),(5723,some (fanBlockRows 59)),(5724,some (fanBlockRows 59)),(5725,some (fanBlockRows 59)),(5726,some (fanBlockRows 59)),(5727,some (fanBlockRows 59)),(5728,some (fanBlockRows 59)),(5729,some (fanBlockRows 59)),(5730,some (fanBlockRows 59)),(5731,some (fanBlockRows 59)),(5732,some (fanBlockRows 59)),(5733,some (fanBlockRows 59)),(5734,some (fanBlockRows 59)),(5735,some (fanBlockRows 59)),(5736,some (fanBlockRows 59)),(5737,some (fanBlockRows 59)),(5738,some (fanBlockRows 59)),(5739,some (fanBlockRows 59)),(5740,some (fanBlockRows 59)),(5741,some (fanBlockRows 59)),(5742,some (fanBlockRows 59)),(5743,some (fanBlockRows 59)),(5744,some (fanBlockRows 59)),(5745,some (fanBlockRows 59)),(5746,some (fanBlockRows 59)),(5747,some (fanBlockRows 59)),(5748,some (fanBlockRows 59)),(5749,some (fanBlockRows 59)),(5750,some (fanBlockRows 59)),(5751,some (fanBlockRows 59)),(5752,some (fanBlockRows 59)),(5753,some (fanBlockRows 59)),(5754,some (fanBlockRows 59)),(5755,some (fanBlockRows 59)),(5756,some (fanBlockRows 59)),(5757,some (fanBlockRows 59)),(5758,some (fanBlockRows 59)),(5759,some (fanBlockRows 59)),(5760,some (fanBlockRows 59)),(5761,some (fanBlockRows 59)),(5762,some (fanBlockRows 59)),(5763,some (fanBlockRows 59)),(5764,some (fanBlockRows 59)),(5765,some (fanBlockRows 59)),(5766,some (fanBlockRows 59)),(5767,some (fanBlockRows 59)),(5768,some (fanBlockRows 59)),(5769,some (fanBlockRows 59)),(5770,some (fanBlockRows 59)),(5771,some (fanBlockRows 59)),(5772,some (fanBlockRows 59)),(5773,some (fanBlockRows 59)),(5774,some (fanBlockRows 59)),(5775,some (fanBlockRows 59)),(5776,some (fanBlockRows 59)),(5777,some (fanBlockRows 59)),(5778,some (fanBlockRows 59)),(5779,some (fanBlockRows 59)),(5780,some (fanBlockRows 2513)),(5781,some (fanBlockRows 2514))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step09.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 27).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain6_8Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step09.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step09.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain6_8Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain6_8Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step09

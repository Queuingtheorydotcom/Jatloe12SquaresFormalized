import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step09
import Compact.HistoricalCommon.C979.Step09Groups00
import Compact.HistoricalCommon.C979.Step09Groups01
import Compact.HistoricalCommon.C979.Step09Groups02
import Compact.HistoricalCommon.C979.Step09Groups03
import Compact.HistoricalCommon.C979.Step09Groups04
import Compact.HistoricalCommon.C979.Step09Groups05
import Compact.HistoricalCommon.C979.Step09Groups06
import Compact.HistoricalCommon.C979.Step09Groups07
import Compact.HistoricalCommon.C979.Step09Groups08

namespace N12Compact.HistoricalCommon.C979.Step09
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 53 (.neighborCut 8 (.sourceCut 13 .leaf (.sourceCut 13 .leaf (.sourceCut 13 .leaf .leaf))) (.neighborCut 8 (.sourceCut 13 (.neighborCut 4 .leaf .leaf) (.sourceCut 13 (.neighborCut 4 .leaf .leaf) (.sourceCut 13 (.neighborCut 4 .leaf .leaf) (.sourceCut 7 .leaf .leaf)))) (.neighborCut 17 .leaf (.sourceCut 26 (.neighborCut 17 (.sourceCut 13 .leaf (.neighborCut 8 .leaf .leaf)) .leaf) .leaf)))) (.neighborCut 4 (.sourceCut 27 .leaf (.sourceCut 13 .leaf .leaf)) (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 17 .leaf (.sourceCut 27 (.neighborCut 17 (.sourceCut 13 .leaf (.neighborCut 8 .leaf (.sourceCut 7 .leaf .leaf))) .leaf) (.neighborCut 17 .leaf (.sourceCut 6 .leaf (.sourceCut 7 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,107,0,67⟩ scopes := by decide +kernel

theorem covered (i : Fin 107) (j : Fin 67) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 107) (j : Fin 67) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context13183_header,context13194_header,context13205_header,context13213_header,context13224_header,context13235_header,context13246_header,context13257_header,context13268_header,context13173_header,context13174_header,context13175_header,context13176_header,context13177_header,context13178_header,context13179_header,context13180_header,context13181_header,context13182_header,context13184_header,context13185_header,context13186_header,context13187_header,context13188_header,context13189_header,context13190_header,context13191_header,context13192_header,context13193_header,context13195_header,context13196_header,context13197_header,context13198_header,context13199_header,context13200_header,context13201_header,context13202_header,context13203_header,context13204_header,context13206_header,context13207_header,context13208_header,context13209_header,context13210_header,context12284_header,context12286_header,context12288_header,context13211_header,context13212_header,context13214_header,context13215_header,context13216_header,context13217_header,context13218_header,context13219_header,context13220_header,context13221_header,context13222_header,context13223_header,context13225_header,context13226_header,context13227_header,context13228_header,context13229_header,context13230_header,context13231_header,context13232_header,context13233_header,context13234_header,context13236_header,context13237_header,context13238_header,context13239_header,context13240_header,context13241_header,context13242_header,context13243_header,context13244_header,context13245_header,context13247_header,context13248_header,context13249_header,context13250_header,context13251_header,context13252_header,context13253_header,context13254_header,context13255_header,context13256_header,context13258_header,context13259_header,context13260_header,context13261_header,context13262_header,context13263_header,context13264_header,context13265_header,context13266_header,context13267_header,context13161_header,context13166_header,context13167_header,context13168_header,context13169_header,context13170_header,context13171_header,context13172_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 107).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(10516,none),(10517,some (fanBlockRows 5559)),(10518,some (fanBlockRows 5570)),(10519,some (fanBlockRows 5581)),(10520,some (fanBlockRows 5589)),(10521,some (fanBlockRows 5600)),(10522,some (fanBlockRows 5611)),(10523,some (fanBlockRows 5622)),(10524,some (fanBlockRows 5633)),(10525,some (fanBlockRows 5644)),(10526,some (fanBlockRows 5549)),(10527,some (fanBlockRows 5550)),(10528,some (fanBlockRows 5551)),(10529,some (fanBlockRows 5552)),(10530,some (fanBlockRows 5553)),(10531,some (fanBlockRows 5554)),(10532,some (fanBlockRows 5555)),(10533,some (fanBlockRows 5556)),(10534,some (fanBlockRows 5557)),(10535,some (fanBlockRows 5558)),(10536,some (fanBlockRows 5560)),(10537,some (fanBlockRows 5561)),(10538,some (fanBlockRows 5562)),(10539,some (fanBlockRows 5563)),(10540,some (fanBlockRows 5564)),(10541,some (fanBlockRows 5565)),(10542,some (fanBlockRows 5566)),(10543,some (fanBlockRows 5567)),(10544,some (fanBlockRows 5568)),(10545,some (fanBlockRows 5569)),(10546,some (fanBlockRows 5571)),(10547,some (fanBlockRows 5572)),(10548,some (fanBlockRows 5573)),(10549,some (fanBlockRows 5574)),(10550,some (fanBlockRows 5575)),(10551,some (fanBlockRows 5576)),(10552,some (fanBlockRows 5577)),(10553,some (fanBlockRows 5578)),(10554,some (fanBlockRows 5579)),(10555,some (fanBlockRows 5580)),(10556,some (fanBlockRows 5582)),(10557,some (fanBlockRows 5583)),(10558,some (fanBlockRows 5584)),(10559,some (fanBlockRows 5585)),(10560,some (fanBlockRows 5586)),(10561,some (fanBlockRows 59)),(10562,some (fanBlockRows 59)),(10563,some (fanBlockRows 59)),(10564,some (fanBlockRows 5587)),(10565,some (fanBlockRows 5588)),(10566,some (fanBlockRows 5590)),(10567,some (fanBlockRows 5591)),(10568,some (fanBlockRows 5592)),(10569,some (fanBlockRows 5593)),(10570,some (fanBlockRows 5594)),(10571,some (fanBlockRows 5595)),(10572,some (fanBlockRows 5596)),(10573,some (fanBlockRows 5597)),(10574,some (fanBlockRows 5598)),(10575,some (fanBlockRows 5599)),(10576,some (fanBlockRows 5601)),(10577,some (fanBlockRows 5602)),(10578,some (fanBlockRows 5603)),(10579,some (fanBlockRows 5604)),(10580,some (fanBlockRows 5605)),(10581,some (fanBlockRows 5606)),(10582,some (fanBlockRows 5607)),(10583,some (fanBlockRows 5608)),(10584,some (fanBlockRows 5609)),(10585,some (fanBlockRows 5610)),(10586,some (fanBlockRows 5612)),(10587,some (fanBlockRows 5613)),(10588,some (fanBlockRows 5614)),(10589,some (fanBlockRows 5615)),(10590,some (fanBlockRows 5616)),(10591,some (fanBlockRows 5617)),(10592,some (fanBlockRows 5618)),(10593,some (fanBlockRows 5619)),(10594,some (fanBlockRows 5620)),(10595,some (fanBlockRows 5621)),(10596,some (fanBlockRows 5623)),(10597,some (fanBlockRows 5624)),(10598,some (fanBlockRows 5625)),(10599,some (fanBlockRows 5626)),(10600,some (fanBlockRows 5627)),(10601,some (fanBlockRows 5628)),(10602,some (fanBlockRows 5629)),(10603,some (fanBlockRows 5630)),(10604,some (fanBlockRows 5631)),(10605,some (fanBlockRows 5632)),(10606,some (fanBlockRows 5634)),(10607,some (fanBlockRows 5635)),(10608,some (fanBlockRows 5636)),(10609,some (fanBlockRows 5637)),(10610,some (fanBlockRows 5638)),(10611,some (fanBlockRows 5639)),(10612,some (fanBlockRows 5640)),(10613,some (fanBlockRows 5641)),(10614,some (fanBlockRows 5642)),(10615,some (fanBlockRows 5643)),(10616,some (fanBlockRows 5541)),(10617,some (fanBlockRows 5542)),(10618,some (fanBlockRows 5543)),(10619,some (fanBlockRows 5544)),(10620,some (fanBlockRows 5545)),(10621,some (fanBlockRows 5546)),(10622,some (fanBlockRows 5547)),(10623,some (fanBlockRows 5548)),(10624,none),(10625,none),(10626,none),(10627,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step09.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 67).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain0_9Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step09.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step09.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain0_9Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain0_9Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step09

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step15
import Compact.HistoricalCommon.C979.Step15Groups00
import Compact.HistoricalCommon.C979.Step15Groups01
import Compact.HistoricalCommon.C979.Step15Groups02
import Compact.HistoricalCommon.C979.Step15Groups03

namespace N12Compact.HistoricalCommon.C979.Step15
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 16 (.sourceCut 45 (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf)) (.sourceCut 23 (.neighborCut 8 .leaf .leaf) .leaf)) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.sourceCut 45 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) (.sourceCut 23 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf))))))

theorem partition_checked : partition.Check ⟨0,91,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 91) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 91) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context10637_header,context10776_header,context10787_header,context10798_header,context10809_header,context10820_header,context10831_header,context10842_header,context10853_header,context10855_header,context10766_header,context10767_header,context10768_header,context10769_header,context10770_header,context10771_header,context10772_header,context10773_header,context10774_header,context10775_header,context10777_header,context10778_header,context10779_header,context10780_header,context10781_header,context10782_header,context10783_header,context10784_header,context10785_header,context10786_header,context10788_header,context10789_header,context10790_header,context10791_header,context10792_header,context10793_header,context10794_header,context10795_header,context10796_header,context10797_header,context10799_header,context10800_header,context10801_header,context10802_header,context10803_header,context10804_header,context10805_header,context10806_header,context10807_header,context10808_header,context10810_header,context10811_header,context10812_header,context10813_header,context10814_header,context10815_header,context10816_header,context10817_header,context10818_header,context10819_header,context10821_header,context10822_header,context10823_header,context10824_header,context10825_header,context10826_header,context10827_header,context10828_header,context10829_header,context10830_header,context10832_header,context10833_header,context10834_header,context10835_header,context10836_header,context10837_header,context10838_header,context10839_header,context10840_header,context10841_header,context10843_header,context10844_header,context10845_header,context10846_header,context10847_header,context10848_header,context10849_header,context10850_header,context10851_header,context10852_header,context10854_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 91).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11714,some (fanBlockRows 4530)),(11715,some (fanBlockRows 4531)),(11716,some (fanBlockRows 4532)),(11717,some (fanBlockRows 4533)),(11718,some (fanBlockRows 59)),(11719,some (fanBlockRows 59)),(11720,some (fanBlockRows 59)),(11721,some (fanBlockRows 59)),(11722,some (fanBlockRows 59)),(11723,some (fanBlockRows 59)),(11724,some (fanBlockRows 59)),(11725,some (fanBlockRows 59)),(11726,some (fanBlockRows 59)),(11727,some (fanBlockRows 59)),(11728,some (fanBlockRows 59)),(11729,some (fanBlockRows 59)),(11730,some (fanBlockRows 59)),(11731,some (fanBlockRows 59)),(11732,some (fanBlockRows 59)),(11733,some (fanBlockRows 59)),(11734,some (fanBlockRows 59)),(11735,some (fanBlockRows 59)),(11736,some (fanBlockRows 59)),(11737,some (fanBlockRows 59)),(11738,some (fanBlockRows 59)),(11739,some (fanBlockRows 59)),(11740,some (fanBlockRows 59)),(11741,some (fanBlockRows 59)),(11742,some (fanBlockRows 59)),(11743,some (fanBlockRows 59)),(11744,some (fanBlockRows 59)),(11745,some (fanBlockRows 59)),(11746,some (fanBlockRows 59)),(11747,some (fanBlockRows 59)),(11748,some (fanBlockRows 59)),(11749,some (fanBlockRows 59)),(11750,some (fanBlockRows 59)),(11751,some (fanBlockRows 59)),(11752,some (fanBlockRows 59)),(11753,some (fanBlockRows 59)),(11754,some (fanBlockRows 59)),(11755,some (fanBlockRows 59)),(11756,some (fanBlockRows 59)),(11757,some (fanBlockRows 59)),(11758,some (fanBlockRows 59)),(11759,some (fanBlockRows 59)),(11760,some (fanBlockRows 59)),(11761,some (fanBlockRows 59)),(11762,some (fanBlockRows 59)),(11763,some (fanBlockRows 59)),(11764,some (fanBlockRows 59)),(11765,some (fanBlockRows 59)),(11766,some (fanBlockRows 59)),(11767,some (fanBlockRows 59)),(11768,some (fanBlockRows 59)),(11769,some (fanBlockRows 59)),(11770,some (fanBlockRows 59)),(11771,some (fanBlockRows 59)),(11772,some (fanBlockRows 59)),(11773,some (fanBlockRows 59)),(11774,some (fanBlockRows 59)),(11775,some (fanBlockRows 59)),(11776,some (fanBlockRows 59)),(11777,some (fanBlockRows 59)),(11778,some (fanBlockRows 59)),(11779,some (fanBlockRows 59)),(11780,some (fanBlockRows 4534)),(11781,some (fanBlockRows 4535)),(11782,some (fanBlockRows 4536)),(11783,some (fanBlockRows 4537)),(11784,some (fanBlockRows 4538)),(11785,some (fanBlockRows 4539)),(11786,some (fanBlockRows 4540)),(11787,some (fanBlockRows 4541)),(11788,some (fanBlockRows 4542)),(11789,some (fanBlockRows 4543)),(11790,some (fanBlockRows 4544)),(11791,some (fanBlockRows 4545)),(11792,some (fanBlockRows 4546)),(11793,some (fanBlockRows 4547)),(11794,some (fanBlockRows 4548)),(11795,some (fanBlockRows 4549)),(11796,some (fanBlockRows 4550)),(11797,some (fanBlockRows 4551)),(11798,some (fanBlockRows 4552)),(11799,some (fanBlockRows 4553)),(11800,some (fanBlockRows 4554)),(11801,some (fanBlockRows 4555)),(11802,some (fanBlockRows 4556)),(11803,some (fanBlockRows 4557)),(11804,some (fanBlockRows 4558))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step15.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain11_7Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step15.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step15.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain11_7Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain11_7Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step15

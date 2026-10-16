import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step10
import Compact.HistoricalCommon.C979.Step10Groups00
import Compact.HistoricalCommon.C979.Step10Groups01
import Compact.HistoricalCommon.C979.Step10Groups02
import Compact.HistoricalCommon.C979.Step10Groups03

namespace N12Compact.HistoricalCommon.C979.Step10
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 16 (.sourceCut 11 (.neighborCut 8 .leaf (.neighborCut 4 .leaf .leaf)) .leaf) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.sourceCut 11 (.neighborCut 2 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,23,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 23) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 23) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context9756_header,context9885_header,context9886_header,context9887_header,context9888_header,context9889_header,context9890_header,context9891_header,context9892_header,context9893_header,context9894_header,context9895_header,context9896_header,context9897_header,context9898_header,context9899_header,context9900_header,context9901_header,context9902_header,context9903_header,context9904_header,context9905_header,context9906_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 23).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(10737,none),(10738,none),(10739,none),(10740,none),(10741,none),(10742,none),(10743,none),(10744,none),(10745,none),(10746,none),(10747,none),(10748,none),(10749,none),(10750,none),(10751,none),(10752,none),(10753,none),(10754,none),(10755,none),(10756,none),(10757,none),(10758,none),(10759,none),(10760,none),(10761,none),(10762,none),(10763,none),(10764,none),(10765,none),(10766,none),(10767,none),(10768,none),(10769,none),(10770,none),(10771,none),(10772,none),(10773,none),(10774,none),(10775,none),(10776,none),(10777,none),(10778,none),(10779,none),(10780,none),(10781,none),(10782,none),(10783,none),(10784,none),(10785,none),(10786,none),(10787,none),(10788,none),(10789,none),(10790,none),(10791,none),(10792,none),(10793,none),(10794,none),(10795,none),(10796,none),(10797,none),(10798,none),(10799,none),(10800,none),(10801,none),(10802,none),(10803,none),(10804,none),(10805,none),(10806,none),(10807,none),(10808,none),(10809,none),(10810,none),(10811,none),(10812,none),(10813,none),(10814,none),(10815,none),(10816,none),(10817,none),(10818,none),(10819,none),(10820,none),(10821,none),(10822,none),(10823,none),(10824,none),(10825,none),(10826,none),(10827,none),(10828,none),(10829,none),(10830,none),(10831,none),(10832,none),(10833,none),(10834,none),(10835,none),(10836,none),(10837,none),(10838,none),(10839,none),(10840,some (fanBlockRows 4120)),(10841,some (fanBlockRows 4121)),(10842,some (fanBlockRows 4122)),(10843,some (fanBlockRows 4123)),(10844,some (fanBlockRows 4124)),(10845,some (fanBlockRows 4125)),(10846,some (fanBlockRows 4126)),(10847,some (fanBlockRows 4127)),(10848,some (fanBlockRows 4128)),(10849,some (fanBlockRows 4129)),(10850,some (fanBlockRows 4130)),(10851,some (fanBlockRows 4131)),(10852,some (fanBlockRows 4132)),(10853,some (fanBlockRows 4133)),(10854,some (fanBlockRows 4134)),(10855,some (fanBlockRows 4135)),(10856,some (fanBlockRows 4136)),(10857,some (fanBlockRows 4137)),(10858,some (fanBlockRows 4138)),(10859,some (fanBlockRows 4139)),(10860,some (fanBlockRows 4140)),(10861,some (fanBlockRows 4141)),(10862,some (fanBlockRows 4142)),(10863,none),(10864,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step10.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain2_2Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step10.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step10.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain2_2Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain2_2Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step10

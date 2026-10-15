import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step20
import Compact.HistoricalCommon.C973.Step20Groups00
import Compact.HistoricalCommon.C973.Step20Groups01
import Compact.HistoricalCommon.C973.Step20Groups02
import Compact.HistoricalCommon.C973.Step20Groups03
import Compact.HistoricalCommon.C973.Step20Groups04
import Compact.HistoricalCommon.C973.Step20Groups05
import Compact.HistoricalCommon.C973.Step20Groups06
import Compact.HistoricalCommon.C973.Step20Groups07

namespace N12Compact.HistoricalCommon.C973.Step20
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.neighborCut 8 (.sourceCut 6 .leaf (.sourceCut 7 (.neighborCut 4 .leaf .leaf) (.sourceCut 13 .leaf (.sourceCut 6 .leaf (.sourceCut 7 (.neighborCut 4 .leaf .leaf) (.neighborCut 4 .leaf .leaf)))))) (.neighborCut 8 (.sourceCut 13 .leaf (.sourceCut 6 .leaf (.sourceCut 7 .leaf .leaf))) (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 6 (.neighborCut 8 .leaf .leaf) (.sourceCut 7 .leaf .leaf))) (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.sourceCut 6 .leaf .leaf))) (.sourceCut 13 (.neighborCut 8 (.sourceCut 6 .leaf .leaf) .leaf) (.sourceCut 13 (.neighborCut 4 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 8 (.sourceCut 6 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,52,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 52) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 52) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context7574_header,context7585_header,context7588_header,context7589_header,context7590_header,context7591_header,context7474_header,context7541_header,context7542_header,context7543_header,context7544_header,context7545_header,context7546_header,context7547_header,context7548_header,context7549_header,context7550_header,context7551_header,context7552_header,context7553_header,context7554_header,context7555_header,context7556_header,context7557_header,context7558_header,context7559_header,context7560_header,context7561_header,context7562_header,context7563_header,context7564_header,context7565_header,context7566_header,context7567_header,context7568_header,context7569_header,context7570_header,context7571_header,context7572_header,context7573_header,context7575_header,context7576_header,context7577_header,context7578_header,context7579_header,context7580_header,context7581_header,context7582_header,context7583_header,context7584_header,context7586_header,context7587_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 52).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6724,none),(6725,none),(6726,none),(6727,none),(6728,some (fanBlockRows 3065)),(6729,some (fanBlockRows 3076)),(6730,some (fanBlockRows 3079)),(6731,some (fanBlockRows 3080)),(6732,some (fanBlockRows 3081)),(6733,some (fanBlockRows 3082)),(6734,some (fanBlockRows 3031)),(6735,some (fanBlockRows 3032)),(6736,some (fanBlockRows 3033)),(6737,some (fanBlockRows 3034)),(6738,some (fanBlockRows 3035)),(6739,some (fanBlockRows 3036)),(6740,some (fanBlockRows 3037)),(6741,some (fanBlockRows 3038)),(6742,none),(6743,none),(6744,none),(6745,none),(6746,none),(6747,some (fanBlockRows 3039)),(6748,some (fanBlockRows 3040)),(6749,some (fanBlockRows 3041)),(6750,some (fanBlockRows 3042)),(6751,some (fanBlockRows 3043)),(6752,some (fanBlockRows 3044)),(6753,none),(6754,some (fanBlockRows 3045)),(6755,some (fanBlockRows 3046)),(6756,some (fanBlockRows 3047)),(6757,some (fanBlockRows 3048)),(6758,some (fanBlockRows 3049)),(6759,some (fanBlockRows 3050)),(6760,some (fanBlockRows 3051)),(6761,some (fanBlockRows 3052)),(6762,some (fanBlockRows 3053)),(6763,some (fanBlockRows 3054)),(6764,some (fanBlockRows 3055)),(6765,some (fanBlockRows 3056)),(6766,some (fanBlockRows 3057)),(6767,some (fanBlockRows 3058)),(6768,some (fanBlockRows 3059)),(6769,some (fanBlockRows 3060)),(6770,some (fanBlockRows 3061)),(6771,some (fanBlockRows 3062)),(6772,some (fanBlockRows 3063)),(6773,some (fanBlockRows 3064)),(6774,some (fanBlockRows 3066)),(6775,some (fanBlockRows 3067)),(6776,some (fanBlockRows 3068)),(6777,some (fanBlockRows 3069)),(6778,some (fanBlockRows 3070)),(6779,some (fanBlockRows 3071)),(6780,some (fanBlockRows 3072)),(6781,some (fanBlockRows 3073)),(6782,some (fanBlockRows 3074)),(6783,some (fanBlockRows 3075)),(6784,some (fanBlockRows 3077)),(6785,some (fanBlockRows 3078)),(6786,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step20.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain1_20Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step20.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step20.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain1_20Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain1_20Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step20

import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C973.DirectPruning.Step14
import Compact.HistoricalCommon.C973.Step14Groups00
import Compact.HistoricalCommon.C973.Step14Groups01
import Compact.HistoricalCommon.C973.Step14Groups02
import Compact.HistoricalCommon.C973.Step14Groups03
import Compact.HistoricalCommon.C973.Step14Groups04

namespace N12Compact.HistoricalCommon.C973.Step14
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 28 (.neighborCut 6 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 13 .leaf (.neighborCut 7 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf)))))))) (.neighborCut 6 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.neighborCut 13 .leaf (.neighborCut 7 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,56,0,54⟩ scopes := by decide +kernel

theorem covered (i : Fin 56) (j : Fin 54) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 56) (j : Fin 54) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context6958_header,context6959_header,context6960_header,context6850_header,context6905_header,context6906_header,context6907_header,context6908_header,context6909_header,context6910_header,context6911_header,context6912_header,context6913_header,context6914_header,context6915_header,context6916_header,context6917_header,context6918_header,context6919_header,context6920_header,context6921_header,context6922_header,context6924_header,context6925_header,context6926_header,context6927_header,context6928_header,context6929_header,context6930_header,context6931_header,context6932_header,context6933_header,context6934_header,context6935_header,context6936_header,context6937_header,context6938_header,context6939_header,context6940_header,context6941_header,context6942_header,context6943_header,context6944_header,context6945_header,context6946_header,context6947_header,context6948_header,context6949_header,context6950_header,context6951_header,context6952_header,context6953_header,context6954_header,context6955_header,context6956_header,context6957_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 56).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(6683,none),(6684,none),(6685,none),(6686,none),(6687,none),(6688,none),(6689,none),(6690,some (fanBlockRows 2785)),(1197,some (fanBlockRows 2786)),(1198,some (fanBlockRows 2787)),(1199,some (fanBlockRows 2733)),(1200,some (fanBlockRows 2734)),(1201,some (fanBlockRows 2735)),(1202,some (fanBlockRows 2736)),(1203,some (fanBlockRows 2737)),(1204,some (fanBlockRows 2738)),(1205,some (fanBlockRows 2739)),(1206,some (fanBlockRows 2740)),(1207,some (fanBlockRows 2741)),(1208,some (fanBlockRows 2742)),(1209,some (fanBlockRows 2743)),(1210,some (fanBlockRows 2744)),(1211,some (fanBlockRows 2745)),(6691,some (fanBlockRows 2746)),(6692,some (fanBlockRows 2747)),(6693,some (fanBlockRows 2748)),(6694,some (fanBlockRows 2749)),(6695,some (fanBlockRows 2750)),(6696,some (fanBlockRows 2751)),(1218,some (fanBlockRows 59)),(1219,some (fanBlockRows 2752)),(1220,some (fanBlockRows 2753)),(1221,some (fanBlockRows 2754)),(1222,some (fanBlockRows 2755)),(1223,some (fanBlockRows 2756)),(1224,some (fanBlockRows 2757)),(1225,some (fanBlockRows 2758)),(6697,some (fanBlockRows 2759)),(6698,some (fanBlockRows 2760)),(6699,some (fanBlockRows 2761)),(6700,some (fanBlockRows 2762)),(6701,some (fanBlockRows 2763)),(6702,some (fanBlockRows 2764)),(6703,some (fanBlockRows 2765)),(6704,some (fanBlockRows 2766)),(6705,some (fanBlockRows 2767)),(6706,some (fanBlockRows 2768)),(6707,some (fanBlockRows 2769)),(6708,some (fanBlockRows 2770)),(6709,some (fanBlockRows 2771)),(6710,some (fanBlockRows 2772)),(6711,some (fanBlockRows 2773)),(6712,some (fanBlockRows 2774)),(6713,some (fanBlockRows 2775)),(6714,some (fanBlockRows 2776)),(6715,some (fanBlockRows 2777)),(6716,some (fanBlockRows 2778)),(6717,some (fanBlockRows 2779)),(6718,some (fanBlockRows 2780)),(6719,some (fanBlockRows 2781)),(6720,some (fanBlockRows 2782)),(6721,some (fanBlockRows 2783)),(6722,some (fanBlockRows 2784)),(6723,none)]

theorem planHeaders_exact :
    N12Compact.C973DirectPruning.Step14.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 54).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C973.continuousScout973Domain8_10Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C973DirectPruning.Step14.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C973DirectPruning.Step14.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C973.continuousScout973Domain8_10Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C973.continuousScout973Domain8_10Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C973.Step14

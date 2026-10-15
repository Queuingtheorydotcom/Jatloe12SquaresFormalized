import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step09
import Compact.HistoricalCommon.C701.Step09Groups00
import Compact.HistoricalCommon.C701.Step09Groups01
import Compact.HistoricalCommon.C701.Step09Groups02
import Compact.HistoricalCommon.C701.Step09Groups03
import Compact.HistoricalCommon.C701.Step09Groups04
import Compact.HistoricalCommon.C701.Step09Groups05
import Compact.HistoricalCommon.C701.Step09Groups06
import Compact.HistoricalCommon.C701.Step09Groups07
import Compact.HistoricalCommon.C701.Step09Groups08
import Compact.HistoricalCommon.C701.Step09Groups09
import Compact.HistoricalCommon.C701.Step09Groups10
import Compact.HistoricalCommon.C701.Step09Groups11

namespace N12Compact.HistoricalCommon.C701.Step09
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44,group45,group46]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope,group45_scope,group46_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 27 (.neighborCut 8 (.sourceCut 13 .leaf (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf))) (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.sourceCut 13 (.neighborCut 8 .leaf (.neighborCut 16 .leaf (.neighborCut 8 (.sourceCut 6 .leaf .leaf) .leaf))) (.neighborCut 8 (.sourceCut 7 .leaf (.neighborCut 4 .leaf .leaf)) (.neighborCut 16 (.sourceCut 7 .leaf (.sourceCut 3 .leaf (.neighborCut 8 .leaf .leaf))) .leaf)))))) (.neighborCut 2 .leaf (.neighborCut 2 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.sourceCut 6 (.neighborCut 8 .leaf (.neighborCut 4 .leaf (.neighborCut 4 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))))) (.sourceCut 7 (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.neighborCut 8 .leaf (.sourceCut 3 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))))) (.neighborCut 16 .leaf (.neighborCut 8 .leaf (.sourceCut 7 (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 (.sourceCut 3 .leaf .leaf) (.neighborCut 4 .leaf .leaf)))))))))))))

theorem partition_checked : partition.Check ⟨0,54,0,64⟩ scopes := by decide +kernel

theorem covered (i : Fin 54) (j : Fin 64) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 54) (j : Fin 64) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1748_header,context1759_header,context1765_header,context1776_header,context1787_header,context1788_header,context1789_header,context1790_header,context1791_header,context1698_header,context1739_header,context1740_header,context1741_header,context1742_header,context1743_header,context1744_header,context1745_header,context1746_header,context1747_header,context1749_header,context1750_header,context1751_header,context1752_header,context1753_header,context1754_header,context1755_header,context1756_header,context1757_header,context1758_header,context1760_header,context1761_header,context1762_header,context1763_header,context1764_header,context1766_header,context1767_header,context1768_header,context1769_header,context1770_header,context1771_header,context1772_header,context1773_header,context1774_header,context1775_header,context1777_header,context1778_header,context1779_header,context1780_header,context1781_header,context1782_header,context1783_header,context1784_header,context1785_header,context1786_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 54).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1189,none),(1190,some (fanBlockRows 657)),(1191,some (fanBlockRows 668)),(1192,some (fanBlockRows 674)),(1193,some (fanBlockRows 685)),(1194,some (fanBlockRows 696)),(1195,some (fanBlockRows 697)),(1196,some (fanBlockRows 698)),(1197,some (fanBlockRows 699)),(1198,some (fanBlockRows 700)),(1199,some (fanBlockRows 647)),(1200,some (fanBlockRows 648)),(1201,some (fanBlockRows 649)),(1202,some (fanBlockRows 650)),(1203,some (fanBlockRows 651)),(1204,some (fanBlockRows 652)),(1205,some (fanBlockRows 653)),(1206,some (fanBlockRows 654)),(1207,some (fanBlockRows 655)),(1208,some (fanBlockRows 656)),(1209,some (fanBlockRows 658)),(1210,some (fanBlockRows 659)),(1211,some (fanBlockRows 660)),(1212,some (fanBlockRows 661)),(1213,some (fanBlockRows 662)),(1214,some (fanBlockRows 663)),(1215,some (fanBlockRows 664)),(1216,some (fanBlockRows 665)),(1217,some (fanBlockRows 666)),(1218,some (fanBlockRows 667)),(1219,none),(1220,none),(1221,none),(1222,none),(1223,none),(1224,some (fanBlockRows 669)),(1225,some (fanBlockRows 670)),(1226,some (fanBlockRows 671)),(1227,some (fanBlockRows 672)),(1228,some (fanBlockRows 673)),(1229,some (fanBlockRows 675)),(1230,some (fanBlockRows 676)),(1231,some (fanBlockRows 677)),(1232,some (fanBlockRows 678)),(1233,some (fanBlockRows 679)),(1234,some (fanBlockRows 680)),(1235,some (fanBlockRows 681)),(1236,some (fanBlockRows 682)),(1237,some (fanBlockRows 683)),(1238,some (fanBlockRows 684)),(1239,some (fanBlockRows 686)),(1240,some (fanBlockRows 687)),(1241,some (fanBlockRows 688)),(1242,some (fanBlockRows 689)),(1243,some (fanBlockRows 690)),(1244,some (fanBlockRows 691)),(1245,some (fanBlockRows 692)),(1246,some (fanBlockRows 693)),(1247,some (fanBlockRows 694)),(1248,some (fanBlockRows 695)),(1249,none),(1250,none),(1251,none),(1252,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step09.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 64).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain0_1Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step09.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step09.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain0_1Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain0_1Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step09

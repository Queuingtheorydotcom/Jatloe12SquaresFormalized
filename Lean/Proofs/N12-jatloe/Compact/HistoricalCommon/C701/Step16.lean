import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step16
import Compact.HistoricalCommon.C701.Step16Groups00
import Compact.HistoricalCommon.C701.Step16Groups01
import Compact.HistoricalCommon.C701.Step16Groups02
import Compact.HistoricalCommon.C701.Step16Groups03
import Compact.HistoricalCommon.C701.Step16Groups04
import Compact.HistoricalCommon.C701.Step16Groups05
import Compact.HistoricalCommon.C701.Step16Groups06
import Compact.HistoricalCommon.C701.Step16Groups07
import Compact.HistoricalCommon.C701.Step16Groups08
import Compact.HistoricalCommon.C701.Step16Groups09
import Compact.HistoricalCommon.C701.Step16Groups10

namespace N12Compact.HistoricalCommon.C701.Step16
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 5 (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 3 .leaf (.sourceCut 2 (.neighborCut 2 .leaf (.sourceCut 1 .leaf .leaf)) .leaf)))) (.sourceCut 6 (.neighborCut 2 .leaf (.neighborCut 3 .leaf .leaf)) (.sourceCut 6 (.neighborCut 2 .leaf (.neighborCut 3 .leaf .leaf)) (.sourceCut 6 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.sourceCut 3 .leaf (.neighborCut 2 .leaf (.sourceCut 1 .leaf .leaf))))) (.sourceCut 6 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))))) (.sourceCut 6 (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf)))))) (.sourceCut 6 (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))))) (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))))))))))))

theorem partition_checked : partition.Check ⟨0,47,0,10⟩ scopes := by decide +kernel

theorem covered (i : Fin 47) (j : Fin 10) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 47) (j : Fin 10) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context618_header,context629_header,context638_header,context646_header,context656_header,context660_header,context661_header,context662_header,context663_header,context664_header,context619_header,context620_header,context621_header,context622_header,context623_header,context624_header,context625_header,context626_header,context627_header,context628_header,context630_header,context631_header,context632_header,context633_header,context634_header,context635_header,context636_header,context637_header,context639_header,context640_header,context641_header,context642_header,context643_header,context644_header,context645_header,context647_header,context648_header,context649_header,context650_header,context651_header,context652_header,context653_header,context654_header,context655_header,context657_header,context658_header,context659_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 47).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1834,some (fanBlockRows 223)),(1835,some (fanBlockRows 233)),(1836,some (fanBlockRows 242)),(1837,some (fanBlockRows 250)),(1838,some (fanBlockRows 260)),(1839,some (fanBlockRows 264)),(1840,some (fanBlockRows 265)),(1841,some (fanBlockRows 266)),(1842,some (fanBlockRows 267)),(1843,some (fanBlockRows 268)),(1844,some (fanBlockRows 224)),(1845,some (fanBlockRows 225)),(1846,some (fanBlockRows 226)),(1847,some (fanBlockRows 227)),(1848,some (fanBlockRows 228)),(1849,some (fanBlockRows 229)),(1850,some (fanBlockRows 230)),(1851,some (fanBlockRows 231)),(1852,some (fanBlockRows 232)),(1853,some (fanBlockRows 59)),(1854,none),(1855,none),(1856,some (fanBlockRows 234)),(1857,some (fanBlockRows 235)),(1858,some (fanBlockRows 236)),(1859,some (fanBlockRows 237)),(1860,some (fanBlockRows 238)),(1861,some (fanBlockRows 239)),(1862,some (fanBlockRows 240)),(1863,some (fanBlockRows 241)),(1864,some (fanBlockRows 243)),(1865,some (fanBlockRows 244)),(1866,some (fanBlockRows 245)),(1867,some (fanBlockRows 246)),(1868,some (fanBlockRows 247)),(1869,some (fanBlockRows 248)),(1870,some (fanBlockRows 249)),(1871,none),(1872,none),(1873,none),(1874,none),(1875,some (fanBlockRows 251)),(1876,some (fanBlockRows 252)),(1877,some (fanBlockRows 253)),(1878,some (fanBlockRows 254)),(1879,some (fanBlockRows 255)),(1880,some (fanBlockRows 256)),(1881,some (fanBlockRows 257)),(1882,some (fanBlockRows 258)),(1883,some (fanBlockRows 259)),(1884,some (fanBlockRows 261)),(1885,some (fanBlockRows 262)),(1886,some (fanBlockRows 263))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step16.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 10).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain6_13Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step16.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step16.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain6_13Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain6_13Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step16

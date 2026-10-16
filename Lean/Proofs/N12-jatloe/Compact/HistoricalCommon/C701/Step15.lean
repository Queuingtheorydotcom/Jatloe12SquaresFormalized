import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step15
import Compact.HistoricalCommon.C701.Step15Groups00
import Compact.HistoricalCommon.C701.Step15Groups01
import Compact.HistoricalCommon.C701.Step15Groups02
import Compact.HistoricalCommon.C701.Step15Groups03
import Compact.HistoricalCommon.C701.Step15Groups04
import Compact.HistoricalCommon.C701.Step15Groups05
import Compact.HistoricalCommon.C701.Step15Groups06
import Compact.HistoricalCommon.C701.Step15Groups07
import Compact.HistoricalCommon.C701.Step15Groups08
import Compact.HistoricalCommon.C701.Step15Groups09

namespace N12Compact.HistoricalCommon.C701.Step15
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 12 (.neighborCut 12 (.sourceCut 6 (.neighborCut 6 .leaf .leaf) .leaf) (.neighborCut 6 (.sourceCut 3 .leaf (.sourceCut 1 .leaf (.sourceCut 2 .leaf .leaf))) .leaf)) (.sourceCut 6 (.neighborCut 6 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf .leaf))) (.sourceCut 1 (.neighborCut 12 .leaf .leaf) (.sourceCut 2 (.neighborCut 12 .leaf .leaf) (.sourceCut 4 (.neighborCut 12 .leaf .leaf) (.sourceCut 12 (.neighborCut 3 (.sourceCut 6 .leaf .leaf) (.neighborCut 3 (.sourceCut 6 .leaf .leaf) (.neighborCut 6 (.sourceCut 6 (.neighborCut 3 .leaf .leaf) (.sourceCut 3 .leaf .leaf)) .leaf))) (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 6 .leaf (.sourceCut 6 (.neighborCut 3 .leaf (.neighborCut 3 .leaf .leaf)) (.neighborCut 6 .leaf (.sourceCut 3 .leaf (.neighborCut 3 .leaf .leaf))))))))))))))

theorem partition_checked : partition.Check ⟨0,50,0,25⟩ scopes := by decide +kernel

theorem covered (i : Fin 50) (j : Fin 25) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 50) (j : Fin 25) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context578_header,context589_header,context598_header,context609_header,context613_header,context614_header,context615_header,context616_header,context617_header,context543_header,context569_header,context570_header,context571_header,context572_header,context573_header,context574_header,context575_header,context576_header,context577_header,context579_header,context580_header,context581_header,context582_header,context583_header,context584_header,context585_header,context586_header,context587_header,context588_header,context590_header,context591_header,context592_header,context593_header,context594_header,context595_header,context596_header,context597_header,context599_header,context600_header,context601_header,context602_header,context603_header,context604_header,context605_header,context606_header,context607_header,context608_header,context610_header,context611_header,context612_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 50).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1775,none),(1776,some (fanBlockRows 189)),(1777,some (fanBlockRows 194)),(1778,some (fanBlockRows 203)),(1779,some (fanBlockRows 214)),(1780,some (fanBlockRows 218)),(1781,some (fanBlockRows 219)),(1782,some (fanBlockRows 220)),(1783,some (fanBlockRows 221)),(1784,some (fanBlockRows 222)),(1785,some (fanBlockRows 179)),(1786,some (fanBlockRows 180)),(1787,some (fanBlockRows 181)),(1788,some (fanBlockRows 182)),(1789,some (fanBlockRows 183)),(1790,some (fanBlockRows 184)),(1791,some (fanBlockRows 185)),(1792,some (fanBlockRows 186)),(1793,some (fanBlockRows 187)),(1794,some (fanBlockRows 188)),(1795,some (fanBlockRows 59)),(1796,some (fanBlockRows 59)),(1797,some (fanBlockRows 59)),(1798,some (fanBlockRows 59)),(1799,some (fanBlockRows 59)),(1800,some (fanBlockRows 59)),(1801,some (fanBlockRows 190)),(1802,some (fanBlockRows 191)),(1803,some (fanBlockRows 192)),(1804,some (fanBlockRows 193)),(1805,some (fanBlockRows 195)),(1806,some (fanBlockRows 196)),(1807,some (fanBlockRows 197)),(1808,some (fanBlockRows 198)),(1809,some (fanBlockRows 199)),(1810,some (fanBlockRows 200)),(1811,none),(1812,none),(1813,some (fanBlockRows 201)),(1814,some (fanBlockRows 202)),(1815,some (fanBlockRows 204)),(1816,some (fanBlockRows 205)),(1817,some (fanBlockRows 206)),(1818,some (fanBlockRows 207)),(1819,some (fanBlockRows 208)),(1820,some (fanBlockRows 209)),(1821,some (fanBlockRows 210)),(1822,some (fanBlockRows 211)),(1823,some (fanBlockRows 212)),(1824,some (fanBlockRows 213)),(1825,some (fanBlockRows 215)),(1826,some (fanBlockRows 216)),(1827,some (fanBlockRows 217)),(1828,none),(1829,none),(1830,none),(1831,none),(1832,none),(1833,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step15.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 25).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain2_5Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step15.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step15.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain2_5Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain2_5Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step15

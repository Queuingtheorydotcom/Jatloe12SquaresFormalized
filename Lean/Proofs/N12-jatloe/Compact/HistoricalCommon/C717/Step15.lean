import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step15
import Compact.HistoricalCommon.C717.Step15Groups00
import Compact.HistoricalCommon.C717.Step15Groups01
import Compact.HistoricalCommon.C717.Step15Groups02
import Compact.HistoricalCommon.C717.Step15Groups03
import Compact.HistoricalCommon.C717.Step15Groups04
import Compact.HistoricalCommon.C717.Step15Groups05
import Compact.HistoricalCommon.C717.Step15Groups06
import Compact.HistoricalCommon.C717.Step15Groups07
import Compact.HistoricalCommon.C717.Step15Groups08
import Compact.HistoricalCommon.C717.Step15Groups09
import Compact.HistoricalCommon.C717.Step15Groups10

namespace N12Compact.HistoricalCommon.C717.Step15
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 64 (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 16 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf))) (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))))))))) (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)))) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 32 .leaf .leaf) (.sourceCut 16 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 8 .leaf .leaf) .leaf)) (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 8 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,128,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context4622_header,context4789_header,context4800_header,context4811_header,context4822_header,context4833_header,context4844_header,context4857_header,context4878_header,context4892_header,context4761_header,context4772_header,context4781_header,context4782_header,context4783_header,context4784_header,context4785_header,context4786_header,context4787_header,context4788_header,context4790_header,context4791_header,context4792_header,context4793_header,context4794_header,context4795_header,context4796_header,context4797_header,context4798_header,context4799_header,context4801_header,context4802_header,context4803_header,context4804_header,context4805_header,context4806_header,context4807_header,context4808_header,context4809_header,context4810_header,context4812_header,context4813_header,context4814_header,context4815_header,context4816_header,context4817_header,context4818_header,context4819_header,context4820_header,context4821_header,context4823_header,context4824_header,context4825_header,context4826_header,context4827_header,context4828_header,context4829_header,context4830_header,context4831_header,context4832_header,context4834_header,context4835_header,context4836_header,context4837_header,context4838_header,context4839_header,context4840_header,context4841_header,context4842_header,context4843_header,context4845_header,context4846_header,context4847_header,context4848_header,context4849_header,context4850_header,context4851_header,context4852_header,context4854_header,context4856_header,context4859_header,context4861_header,context4863_header,context4865_header,context4867_header,context4869_header,context4871_header,context4873_header,context4875_header,context4877_header,context4880_header,context4882_header,context4884_header,context4885_header,context4886_header,context4887_header,context4888_header,context4889_header,context4890_header,context4891_header,context4751_header,context4752_header,context4753_header,context4754_header,context4755_header,context4756_header,context4757_header,context4758_header,context4759_header,context4760_header,context4762_header,context4763_header,context4764_header,context4765_header,context4766_header,context4767_header,context4768_header,context4769_header,context4770_header,context4771_header,context4773_header,context4774_header,context4775_header,context4776_header,context4777_header,context4778_header,context4779_header,context4780_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(4747,some (fanBlockRows 1732)),(4748,some (fanBlockRows 1771)),(4749,some (fanBlockRows 1782)),(4750,some (fanBlockRows 1793)),(4751,some (fanBlockRows 1804)),(4752,some (fanBlockRows 1815)),(4753,some (fanBlockRows 1826)),(4754,some (fanBlockRows 1835)),(4755,some (fanBlockRows 1836)),(4756,some (fanBlockRows 1844)),(4757,some (fanBlockRows 1743)),(4758,some (fanBlockRows 1754)),(4759,some (fanBlockRows 1763)),(4760,some (fanBlockRows 1764)),(4761,some (fanBlockRows 1765)),(4762,some (fanBlockRows 1766)),(4763,some (fanBlockRows 1767)),(4764,some (fanBlockRows 1768)),(4765,some (fanBlockRows 1769)),(4766,some (fanBlockRows 1770)),(4767,some (fanBlockRows 1772)),(4768,some (fanBlockRows 1773)),(4769,some (fanBlockRows 1774)),(4770,some (fanBlockRows 1775)),(4771,some (fanBlockRows 1776)),(4772,some (fanBlockRows 1777)),(4773,some (fanBlockRows 1778)),(4774,some (fanBlockRows 1779)),(4775,some (fanBlockRows 1780)),(4776,some (fanBlockRows 1781)),(4777,some (fanBlockRows 1783)),(4778,some (fanBlockRows 1784)),(4779,some (fanBlockRows 1785)),(4780,some (fanBlockRows 1786)),(4781,some (fanBlockRows 1787)),(4782,some (fanBlockRows 1788)),(4783,some (fanBlockRows 1789)),(4784,some (fanBlockRows 1790)),(4785,some (fanBlockRows 1791)),(4786,some (fanBlockRows 1792)),(4787,some (fanBlockRows 1794)),(4788,some (fanBlockRows 1795)),(4789,some (fanBlockRows 1796)),(4790,some (fanBlockRows 1797)),(4791,some (fanBlockRows 1798)),(4792,some (fanBlockRows 1799)),(4793,some (fanBlockRows 1800)),(4794,some (fanBlockRows 1801)),(4795,some (fanBlockRows 1802)),(4796,some (fanBlockRows 1803)),(4797,some (fanBlockRows 1805)),(4798,some (fanBlockRows 1806)),(4799,some (fanBlockRows 1807)),(4800,some (fanBlockRows 1808)),(4801,some (fanBlockRows 1809)),(4802,some (fanBlockRows 1810)),(4803,some (fanBlockRows 1811)),(4804,some (fanBlockRows 1812)),(4805,some (fanBlockRows 1813)),(4806,some (fanBlockRows 1814)),(4807,some (fanBlockRows 1816)),(4808,some (fanBlockRows 1817)),(4809,some (fanBlockRows 1818)),(4810,some (fanBlockRows 1819)),(4811,some (fanBlockRows 1820)),(4812,some (fanBlockRows 1821)),(4813,some (fanBlockRows 1822)),(4814,some (fanBlockRows 1823)),(4815,some (fanBlockRows 1824)),(4816,some (fanBlockRows 1825)),(4817,some (fanBlockRows 1827)),(4818,some (fanBlockRows 1828)),(4819,some (fanBlockRows 1829)),(4820,some (fanBlockRows 1830)),(4821,some (fanBlockRows 1831)),(4822,some (fanBlockRows 1832)),(4823,some (fanBlockRows 1833)),(4824,some (fanBlockRows 1834)),(4825,some (fanBlockRows 59)),(4826,some (fanBlockRows 59)),(4827,some (fanBlockRows 59)),(4828,some (fanBlockRows 59)),(4829,some (fanBlockRows 59)),(4830,some (fanBlockRows 59)),(4831,some (fanBlockRows 59)),(4832,some (fanBlockRows 59)),(4833,some (fanBlockRows 59)),(4834,some (fanBlockRows 59)),(4835,some (fanBlockRows 59)),(4836,some (fanBlockRows 59)),(4837,some (fanBlockRows 59)),(4838,some (fanBlockRows 59)),(4839,some (fanBlockRows 59)),(4840,some (fanBlockRows 1837)),(4841,some (fanBlockRows 1838)),(4842,some (fanBlockRows 1839)),(4843,some (fanBlockRows 1840)),(4844,some (fanBlockRows 1841)),(4845,some (fanBlockRows 1842)),(4846,some (fanBlockRows 1843)),(4847,some (fanBlockRows 1733)),(4848,some (fanBlockRows 1734)),(4849,some (fanBlockRows 1735)),(4850,some (fanBlockRows 1736)),(4851,some (fanBlockRows 1737)),(4852,some (fanBlockRows 1738)),(4853,some (fanBlockRows 1739)),(4854,some (fanBlockRows 1740)),(4855,some (fanBlockRows 1741)),(4856,some (fanBlockRows 1742)),(4857,some (fanBlockRows 1744)),(4858,some (fanBlockRows 1745)),(4859,some (fanBlockRows 1746)),(4860,some (fanBlockRows 1747)),(4861,some (fanBlockRows 1748)),(4862,some (fanBlockRows 1749)),(4863,some (fanBlockRows 1750)),(4864,some (fanBlockRows 1751)),(4865,some (fanBlockRows 1752)),(4866,some (fanBlockRows 1753)),(4867,some (fanBlockRows 1755)),(4868,some (fanBlockRows 1756)),(4869,some (fanBlockRows 1757)),(4870,some (fanBlockRows 1758)),(4871,some (fanBlockRows 1759)),(4872,some (fanBlockRows 1760)),(4873,some (fanBlockRows 1761)),(4874,some (fanBlockRows 1762))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step15.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain4_5Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step15.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step15.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain4_5Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain4_5Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step15

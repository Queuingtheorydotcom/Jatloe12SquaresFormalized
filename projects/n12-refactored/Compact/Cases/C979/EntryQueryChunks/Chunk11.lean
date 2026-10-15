import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_5_1 : DirectSingleDomain := ⟨256,1,3,[{0},{2},{0,2},{3},{0,3},{1,3},{0,1,3},{2,3},{0,2,3},{2,5},{0,2,5},{3,5},{0,3,5},{2,3,5},{2,6},{0,2,6},{3,6},{0,3,6},{2,3,6},{2,5,6},{3,5,6}],[N12Compact.C979SharedSelections.selected473,N12Compact.C979SharedSelections.selected474,N12Compact.C979SharedSelections.selected475,N12Compact.HistoricalOwnership.Queries.query1730_certified,N12Compact.HistoricalOwnership.Queries.query1731_certified,N12Compact.C979SharedSelections.selected476,N12Compact.C979SharedSelections.selected477,N12Compact.C979SharedSelections.selected478,N12Compact.HistoricalOwnership.Queries.query1732_certified,N12Compact.C979SharedSelections.selected479,N12Compact.HistoricalOwnership.Queries.query1733_certified,N12Compact.HistoricalOwnership.Queries.query1734_certified,N12Compact.C979SharedSelections.selected480,N12Compact.HistoricalOwnership.Queries.query1735_certified,N12Compact.HistoricalOwnership.Queries.query1736_certified,N12Compact.HistoricalOwnership.Queries.query1737_certified,N12Compact.C979SharedSelections.selected481,N12Compact.C979SharedSelections.selected482,N12Compact.C979SharedSelections.selected483,N12Compact.HistoricalOwnership.Queries.query1738_certified,N12Compact.HistoricalOwnership.Queries.query1739_certified,N12Compact.HistoricalOwnership.Queries.query1740_certified,N12Compact.C979SharedSelections.selected484,N12Compact.HistoricalOwnership.Queries.query1741_certified,N12Compact.HistoricalOwnership.Queries.query1742_certified,N12Compact.HistoricalOwnership.Queries.query1743_certified,N12Compact.HistoricalOwnership.Queries.query1744_certified,N12Compact.C979SharedSelections.selected485,N12Compact.C979SharedSelections.selected486,N12Compact.C979SharedSelections.selected487,N12Compact.HistoricalOwnership.Queries.query1745_certified,N12Compact.HistoricalOwnership.Queries.query1746_certified,N12Compact.HistoricalOwnership.Queries.query1747_certified,N12Compact.C979SharedSelections.selected488,N12Compact.HistoricalOwnership.Queries.query1748_certified,N12Compact.HistoricalOwnership.Queries.query1749_certified,N12Compact.HistoricalOwnership.Queries.query1750_certified,N12Compact.HistoricalOwnership.Queries.query1751_certified,N12Compact.C979SharedSelections.selected489,N12Compact.HistoricalOwnership.Queries.query1752_certified,N12Compact.HistoricalOwnership.Queries.query1753_certified,N12Compact.HistoricalOwnership.Queries.query1754_certified,N12Compact.C979SharedSelections.selected490,N12Compact.C979SharedSelections.selected491,N12Compact.C979SharedSelections.selected492,N12Compact.HistoricalOwnership.Queries.query1755_certified,N12Compact.C979SharedSelections.selected493,N12Compact.HistoricalOwnership.Queries.query1756_certified,N12Compact.HistoricalOwnership.Queries.query1757_certified,N12Compact.C979SharedSelections.selected494,N12Compact.HistoricalOwnership.Queries.query1758_certified,N12Compact.HistoricalOwnership.Queries.query1759_certified,N12Compact.HistoricalOwnership.Queries.query1760_certified,N12Compact.C979SharedSelections.selected495,N12Compact.HistoricalOwnership.Queries.query1761_certified,N12Compact.HistoricalOwnership.Queries.query1762_certified,N12Compact.HistoricalOwnership.Queries.query1763_certified,N12Compact.HistoricalOwnership.Queries.query1764_certified,N12Compact.C979SharedSelections.selected496,N12Compact.HistoricalOwnership.Queries.query1765_certified,N12Compact.HistoricalOwnership.Queries.query1766_certified,N12Compact.HistoricalOwnership.Queries.query1767_certified,N12Compact.HistoricalOwnership.Queries.query1768_certified,N12Compact.HistoricalOwnership.Queries.query1769_certified,N12Compact.C979SharedSelections.selected497,N12Compact.HistoricalOwnership.Queries.query1770_certified,N12Compact.HistoricalOwnership.Queries.query1771_certified,N12Compact.HistoricalOwnership.Queries.query1772_certified,N12Compact.HistoricalOwnership.Queries.query1773_certified,N12Compact.HistoricalOwnership.Queries.query1774_certified,N12Compact.HistoricalOwnership.Queries.query1775_certified,N12Compact.C979SharedSelections.selected498,N12Compact.C979SharedSelections.selected499,N12Compact.C979SharedSelections.selected500,N12Compact.HistoricalOwnership.Queries.query1776_certified,N12Compact.C979SharedSelections.selected501,N12Compact.HistoricalOwnership.Queries.query1777_certified,N12Compact.HistoricalOwnership.Queries.query1778_certified,N12Compact.C979SharedSelections.selected502,N12Compact.HistoricalOwnership.Queries.query1779_certified,N12Compact.HistoricalOwnership.Queries.query1780_certified,N12Compact.HistoricalOwnership.Queries.query1781_certified,N12Compact.C979SharedSelections.selected503,N12Compact.HistoricalOwnership.Queries.query1782_certified,N12Compact.HistoricalOwnership.Queries.query1783_certified,N12Compact.HistoricalOwnership.Queries.query1784_certified,N12Compact.HistoricalOwnership.Queries.query1785_certified,N12Compact.C979SharedSelections.selected504,N12Compact.HistoricalOwnership.Queries.query1786_certified,N12Compact.HistoricalOwnership.Queries.query1787_certified,N12Compact.HistoricalOwnership.Queries.query1788_certified,N12Compact.HistoricalOwnership.Queries.query1789_certified,N12Compact.HistoricalOwnership.Queries.query1790_certified,N12Compact.C979SharedSelections.selected505,N12Compact.HistoricalOwnership.Queries.query1791_certified,N12Compact.HistoricalOwnership.Queries.query1792_certified,N12Compact.HistoricalOwnership.Queries.query1793_certified,N12Compact.HistoricalOwnership.Queries.query1794_certified,N12Compact.HistoricalOwnership.Queries.query1795_certified,N12Compact.HistoricalOwnership.Queries.query1796_certified,N12Compact.C979SharedSelections.selected506,N12Compact.HistoricalOwnership.Queries.query1797_certified,N12Compact.HistoricalOwnership.Queries.query1798_certified,N12Compact.HistoricalOwnership.Queries.query1799_certified,N12Compact.HistoricalOwnership.Queries.query1800_certified,N12Compact.HistoricalOwnership.Queries.query1801_certified,N12Compact.HistoricalOwnership.Queries.query1802_certified,N12Compact.HistoricalOwnership.Queries.query1803_certified,N12Compact.C979SharedSelections.selected507,N12Compact.C979SharedSelections.selected508,N12Compact.C979SharedSelections.selected509,N12Compact.HistoricalOwnership.Queries.query1804_certified,N12Compact.C979SharedSelections.selected510,N12Compact.HistoricalOwnership.Queries.query1805_certified,N12Compact.HistoricalOwnership.Queries.query1806_certified,N12Compact.C979SharedSelections.selected511,N12Compact.HistoricalOwnership.Queries.query1807_certified,N12Compact.HistoricalOwnership.Queries.query1808_certified,N12Compact.HistoricalOwnership.Queries.query1809_certified,N12Compact.C979SharedSelections.selected512,N12Compact.HistoricalOwnership.Queries.query1810_certified,N12Compact.HistoricalOwnership.Queries.query1811_certified,N12Compact.HistoricalOwnership.Queries.query1812_certified,N12Compact.HistoricalOwnership.Queries.query1813_certified,N12Compact.C979SharedSelections.selected513,N12Compact.HistoricalOwnership.Queries.query1814_certified,N12Compact.HistoricalOwnership.Queries.query1815_certified,N12Compact.HistoricalOwnership.Queries.query1816_certified,N12Compact.HistoricalOwnership.Queries.query1817_certified,N12Compact.HistoricalOwnership.Queries.query1818_certified,N12Compact.C979SharedSelections.selected514,N12Compact.HistoricalOwnership.Queries.query1819_certified,N12Compact.HistoricalOwnership.Queries.query1820_certified,N12Compact.HistoricalOwnership.Queries.query1821_certified,N12Compact.HistoricalOwnership.Queries.query1822_certified,N12Compact.HistoricalOwnership.Queries.query1823_certified,N12Compact.HistoricalOwnership.Queries.query1824_certified,N12Compact.C979SharedSelections.selected515,N12Compact.HistoricalOwnership.Queries.query1825_certified,N12Compact.HistoricalOwnership.Queries.query1826_certified,N12Compact.HistoricalOwnership.Queries.query1827_certified,N12Compact.HistoricalOwnership.Queries.query1828_certified,N12Compact.HistoricalOwnership.Queries.query1829_certified,N12Compact.HistoricalOwnership.Queries.query1830_certified,N12Compact.HistoricalOwnership.Queries.query1831_certified,N12Compact.C979SharedSelections.selected516,N12Compact.HistoricalOwnership.Queries.query1832_certified,N12Compact.HistoricalOwnership.Queries.query1833_certified,N12Compact.HistoricalOwnership.Queries.query1834_certified,N12Compact.HistoricalOwnership.Queries.query1835_certified,N12Compact.HistoricalOwnership.Queries.query1836_certified,N12Compact.HistoricalOwnership.Queries.query1837_certified,N12Compact.HistoricalOwnership.Queries.query1838_certified,N12Compact.HistoricalOwnership.Queries.query1839_certified]⟩
private def single979_5_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(256,1,{1}),(256,1,{0,1}),(256,1,{1,2}),(256,1,{0,1,2}),(256,1,{1,2,3}),(256,1,{4}),(256,1,{0,4}),(256,1,{1,4}),(256,1,{0,1,4}),(256,1,{2,4}),(256,1,{0,2,4}),(256,1,{1,2,4}),(256,1,{3,4}),(256,1,{0,3,4}),(256,1,{1,3,4}),(256,1,{2,3,4}),(256,1,{5}),(256,1,{0,5}),(256,1,{1,5}),(256,1,{0,1,5}),(256,1,{1,2,5}),(256,1,{1,3,5}),(256,1,{4,5}),(256,1,{0,4,5}),(256,1,{1,4,5}),(256,1,{2,4,5}),(256,1,{3,4,5}),(256,1,{6}),(256,1,{0,6}),(256,1,{1,6}),(256,1,{0,1,6}),(256,1,{1,2,6}),(256,1,{1,3,6}),(256,1,{4,6}),(256,1,{0,4,6}),(256,1,{1,4,6}),(256,1,{2,4,6}),(256,1,{3,4,6}),(256,1,{5,6}),(256,1,{0,5,6}),(256,1,{1,5,6}),(256,1,{4,5,6}),(256,1,{7}),(256,1,{0,7}),(256,1,{1,7}),(256,1,{0,1,7}),(256,1,{2,7}),(256,1,{0,2,7}),(256,1,{1,2,7}),(256,1,{3,7}),(256,1,{0,3,7}),(256,1,{1,3,7}),(256,1,{2,3,7}),(256,1,{4,7}),(256,1,{0,4,7}),(256,1,{1,4,7}),(256,1,{2,4,7}),(256,1,{3,4,7}),(256,1,{5,7}),(256,1,{0,5,7}),(256,1,{1,5,7}),(256,1,{2,5,7}),(256,1,{3,5,7}),(256,1,{4,5,7}),(256,1,{6,7}),(256,1,{0,6,7}),(256,1,{1,6,7}),(256,1,{2,6,7}),(256,1,{3,6,7}),(256,1,{4,6,7}),(256,1,{5,6,7}),(256,1,{8}),(256,1,{0,8}),(256,1,{1,8}),(256,1,{0,1,8}),(256,1,{2,8}),(256,1,{0,2,8}),(256,1,{1,2,8}),(256,1,{3,8}),(256,1,{0,3,8}),(256,1,{1,3,8}),(256,1,{2,3,8}),(256,1,{4,8}),(256,1,{0,4,8}),(256,1,{1,4,8}),(256,1,{2,4,8}),(256,1,{3,4,8}),(256,1,{5,8}),(256,1,{0,5,8}),(256,1,{1,5,8}),(256,1,{2,5,8}),(256,1,{3,5,8}),(256,1,{4,5,8}),(256,1,{6,8}),(256,1,{0,6,8}),(256,1,{1,6,8}),(256,1,{2,6,8}),(256,1,{3,6,8}),(256,1,{4,6,8}),(256,1,{5,6,8}),(256,1,{7,8}),(256,1,{0,7,8}),(256,1,{1,7,8}),(256,1,{2,7,8}),(256,1,{3,7,8}),(256,1,{4,7,8}),(256,1,{5,7,8}),(256,1,{6,7,8}),(256,1,{9}),(256,1,{0,9}),(256,1,{1,9}),(256,1,{0,1,9}),(256,1,{2,9}),(256,1,{0,2,9}),(256,1,{1,2,9}),(256,1,{3,9}),(256,1,{0,3,9}),(256,1,{1,3,9}),(256,1,{2,3,9}),(256,1,{4,9}),(256,1,{0,4,9}),(256,1,{1,4,9}),(256,1,{2,4,9}),(256,1,{3,4,9}),(256,1,{5,9}),(256,1,{0,5,9}),(256,1,{1,5,9}),(256,1,{2,5,9}),(256,1,{3,5,9}),(256,1,{4,5,9}),(256,1,{6,9}),(256,1,{0,6,9}),(256,1,{1,6,9}),(256,1,{2,6,9}),(256,1,{3,6,9}),(256,1,{4,6,9}),(256,1,{5,6,9}),(256,1,{7,9}),(256,1,{0,7,9}),(256,1,{1,7,9}),(256,1,{2,7,9}),(256,1,{3,7,9}),(256,1,{4,7,9}),(256,1,{5,7,9}),(256,1,{6,7,9}),(256,1,{8,9}),(256,1,{0,8,9}),(256,1,{1,8,9}),(256,1,{2,8,9}),(256,1,{3,8,9}),(256,1,{4,8,9}),(256,1,{5,8,9}),(256,1,{6,8,9}),(256,1,{7,8,9})]
private theorem single979_5_1_queries_exact :
    single979_5_1Signatures = single979_5_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_5_1_queries_exact

private def single979_5_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{0},{2},{0,2},{3},{0,3},{1,3},{0,1,3},{2,3},{0,2,3},{2,5},{0,2,5},{3,5},{0,3,5},{2,3,5},{2,6},{0,2,6},{3,6},{0,3,6},{2,3,6},{2,5,6},{3,5,6}] : List (Finset Nat)) ∨ (256,1,owned) ∈ single979_5_1Signatures

private instance : DecidablePred single979_5_1_owned_claim := fun index => by
  unfold single979_5_1_owned_claim
  infer_instance

private theorem single979_5_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_5_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_5_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_5_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_5_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_5_1 case979Family 1 single979_5_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨256,1,3,[{0},{2},{0,2},{3},{0,3},{1,3},{0,1,3},{2,3},{0,2,3},{2,5},{0,2,5},{3,5},{0,3,5},{2,3,5},{2,6},{0,2,6},{3,6},{0,3,6},{2,3,6},{2,5,6},{3,5,6}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_5_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_5_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_5_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_5_1_owned_block0
      · exact single979_5_1_owned_block1
      · exact single979_5_1_owned_block2
      · exact single979_5_1_owned_block3
      · exact single979_5_1_owned_block4
      · exact single979_5_1_owned_block5
      · exact single979_5_1_owned_block6
      · exact single979_5_1_owned_block7
      · exact single979_5_1_owned_block8
      · exact single979_5_1_owned_block9
      · exact single979_5_1_owned_block10
      · exact single979_5_1_owned_block11
      · exact single979_5_1_owned_block12
      · exact single979_5_1_owned_block13
      · exact single979_5_1_owned_block14
      · exact single979_5_1_owned_block15
      · exact single979_5_1_owned_block16
      · exact single979_5_1_owned_block17
      · exact single979_5_1_owned_block18
      · exact single979_5_1_owned_block19
      · exact single979_5_1_owned_block20
      · exact single979_5_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_5_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_5_1_metadata

theorem single979_5_1_checked : single979_5_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_5_1 case979Family 1
    single979_5_1Signatures single979_5_1_queries_exact (by decide) single979_5_1_metadata

end
end S12

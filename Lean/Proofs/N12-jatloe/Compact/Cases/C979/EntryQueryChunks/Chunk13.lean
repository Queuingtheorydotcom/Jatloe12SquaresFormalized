import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_6_1 : DirectSingleDomain := ⟨512,1,3,[{5},{2,5},{3,5},{2,3,5},{6},{2,6},{3,6},{2,3,6},{5,6},{2,5,6},{3,5,6},{8},{5,8},{2,5,8},{3,5,8},{6,8},{2,6,8},{3,6,8},{5,6,8},{6,9},{6,8,9}],[N12Compact.C979SharedSelections.selected626,N12Compact.C979SharedSelections.selected627,N12Compact.C979SharedSelections.selected628,N12Compact.C979SharedSelections.selected629,N12Compact.C979SharedSelections.selected630,N12Compact.C979SharedSelections.selected631,N12Compact.HistoricalOwnership.Queries.query1910_certified,N12Compact.C979SharedSelections.selected632,N12Compact.C979SharedSelections.selected633,N12Compact.C979SharedSelections.selected634,N12Compact.HistoricalOwnership.Queries.query1911_certified,N12Compact.C979SharedSelections.selected635,N12Compact.HistoricalOwnership.Queries.query1912_certified,N12Compact.HistoricalOwnership.Queries.query1913_certified,N12Compact.C979SharedSelections.selected636,N12Compact.C979SharedSelections.selected637,N12Compact.C979SharedSelections.selected638,N12Compact.HistoricalOwnership.Queries.query1914_certified,N12Compact.C979SharedSelections.selected639,N12Compact.HistoricalOwnership.Queries.query1915_certified,N12Compact.HistoricalOwnership.Queries.query1916_certified,N12Compact.C979SharedSelections.selected640,N12Compact.HistoricalOwnership.Queries.query1917_certified,N12Compact.HistoricalOwnership.Queries.query1918_certified,N12Compact.HistoricalOwnership.Queries.query1919_certified,N12Compact.C979SharedSelections.selected641,N12Compact.C979SharedSelections.selected642,N12Compact.HistoricalOwnership.Queries.query1920_certified,N12Compact.HistoricalOwnership.Queries.query1921_certified,N12Compact.HistoricalOwnership.Queries.query1922_certified,N12Compact.HistoricalOwnership.Queries.query1923_certified,N12Compact.HistoricalOwnership.Queries.query1924_certified,N12Compact.C979SharedSelections.selected643,N12Compact.HistoricalOwnership.Queries.query1925_certified,N12Compact.HistoricalOwnership.Queries.query1926_certified,N12Compact.HistoricalOwnership.Queries.query1927_certified,N12Compact.HistoricalOwnership.Queries.query1928_certified,N12Compact.C979SharedSelections.selected644,N12Compact.C979SharedSelections.selected645,N12Compact.HistoricalOwnership.Queries.query1929_certified,N12Compact.HistoricalOwnership.Queries.query1930_certified,N12Compact.HistoricalOwnership.Queries.query1931_certified,N12Compact.HistoricalOwnership.Queries.query1932_certified,N12Compact.HistoricalOwnership.Queries.query1933_certified,N12Compact.C979SharedSelections.selected646,N12Compact.HistoricalOwnership.Queries.query1934_certified,N12Compact.HistoricalOwnership.Queries.query1935_certified,N12Compact.HistoricalOwnership.Queries.query1936_certified,N12Compact.HistoricalOwnership.Queries.query1937_certified,N12Compact.HistoricalOwnership.Queries.query1938_certified,N12Compact.HistoricalOwnership.Queries.query1939_certified,N12Compact.HistoricalOwnership.Queries.query1940_certified,N12Compact.C979SharedSelections.selected647,N12Compact.C979SharedSelections.selected648,N12Compact.C979SharedSelections.selected649,N12Compact.HistoricalOwnership.Queries.query1941_certified,N12Compact.C979SharedSelections.selected650,N12Compact.HistoricalOwnership.Queries.query1942_certified,N12Compact.HistoricalOwnership.Queries.query1943_certified,N12Compact.C979SharedSelections.selected651,N12Compact.HistoricalOwnership.Queries.query1944_certified,N12Compact.HistoricalOwnership.Queries.query1945_certified,N12Compact.HistoricalOwnership.Queries.query1946_certified,N12Compact.C979SharedSelections.selected652,N12Compact.HistoricalOwnership.Queries.query1947_certified,N12Compact.HistoricalOwnership.Queries.query1948_certified,N12Compact.HistoricalOwnership.Queries.query1949_certified,N12Compact.HistoricalOwnership.Queries.query1950_certified,N12Compact.C979SharedSelections.selected653,N12Compact.HistoricalOwnership.Queries.query1951_certified,N12Compact.HistoricalOwnership.Queries.query1952_certified,N12Compact.HistoricalOwnership.Queries.query1953_certified,N12Compact.HistoricalOwnership.Queries.query1954_certified,N12Compact.HistoricalOwnership.Queries.query1955_certified,N12Compact.C979SharedSelections.selected654,N12Compact.HistoricalOwnership.Queries.query1956_certified,N12Compact.HistoricalOwnership.Queries.query1957_certified,N12Compact.HistoricalOwnership.Queries.query1958_certified,N12Compact.HistoricalOwnership.Queries.query1959_certified,N12Compact.HistoricalOwnership.Queries.query1960_certified,N12Compact.HistoricalOwnership.Queries.query1961_certified,N12Compact.C979SharedSelections.selected655,N12Compact.C979SharedSelections.selected656,N12Compact.HistoricalOwnership.Queries.query1962_certified,N12Compact.C979SharedSelections.selected657,N12Compact.HistoricalOwnership.Queries.query1963_certified,N12Compact.HistoricalOwnership.Queries.query1964_certified,N12Compact.C979SharedSelections.selected658,N12Compact.HistoricalOwnership.Queries.query1965_certified,N12Compact.HistoricalOwnership.Queries.query1966_certified,N12Compact.HistoricalOwnership.Queries.query1967_certified,N12Compact.C979SharedSelections.selected659,N12Compact.HistoricalOwnership.Queries.query1968_certified,N12Compact.HistoricalOwnership.Queries.query1969_certified,N12Compact.HistoricalOwnership.Queries.query1970_certified,N12Compact.HistoricalOwnership.Queries.query1971_certified,N12Compact.HistoricalOwnership.Queries.query1972_certified,N12Compact.HistoricalOwnership.Queries.query1973_certified,N12Compact.HistoricalOwnership.Queries.query1974_certified,N12Compact.HistoricalOwnership.Queries.query1975_certified,N12Compact.HistoricalOwnership.Queries.query1976_certified,N12Compact.HistoricalOwnership.Queries.query1977_certified,N12Compact.C979SharedSelections.selected660,N12Compact.HistoricalOwnership.Queries.query1978_certified,N12Compact.HistoricalOwnership.Queries.query1979_certified,N12Compact.HistoricalOwnership.Queries.query1980_certified,N12Compact.HistoricalOwnership.Queries.query1981_certified,N12Compact.HistoricalOwnership.Queries.query1982_certified,N12Compact.HistoricalOwnership.Queries.query1983_certified,N12Compact.HistoricalOwnership.Queries.query1984_certified,N12Compact.C979SharedSelections.selected661,N12Compact.C979SharedSelections.selected662,N12Compact.C979SharedSelections.selected663,N12Compact.HistoricalOwnership.Queries.query1985_certified,N12Compact.C979SharedSelections.selected664,N12Compact.HistoricalOwnership.Queries.query1986_certified,N12Compact.HistoricalOwnership.Queries.query1987_certified,N12Compact.C979SharedSelections.selected665,N12Compact.HistoricalOwnership.Queries.query1988_certified,N12Compact.HistoricalOwnership.Queries.query1989_certified,N12Compact.HistoricalOwnership.Queries.query1990_certified,N12Compact.C979SharedSelections.selected666,N12Compact.HistoricalOwnership.Queries.query1991_certified,N12Compact.HistoricalOwnership.Queries.query1992_certified,N12Compact.HistoricalOwnership.Queries.query1993_certified,N12Compact.HistoricalOwnership.Queries.query1994_certified,N12Compact.C979SharedSelections.selected667,N12Compact.HistoricalOwnership.Queries.query1995_certified,N12Compact.HistoricalOwnership.Queries.query1996_certified,N12Compact.HistoricalOwnership.Queries.query1997_certified,N12Compact.HistoricalOwnership.Queries.query1998_certified,N12Compact.HistoricalOwnership.Queries.query1999_certified,N12Compact.HistoricalOwnership.Queries.query2000_certified,N12Compact.HistoricalOwnership.Queries.query2001_certified,N12Compact.HistoricalOwnership.Queries.query2002_certified,N12Compact.HistoricalOwnership.Queries.query2003_certified,N12Compact.HistoricalOwnership.Queries.query2004_certified,N12Compact.HistoricalOwnership.Queries.query2005_certified,N12Compact.C979SharedSelections.selected668,N12Compact.HistoricalOwnership.Queries.query2006_certified,N12Compact.HistoricalOwnership.Queries.query2007_certified,N12Compact.HistoricalOwnership.Queries.query2008_certified,N12Compact.HistoricalOwnership.Queries.query2009_certified,N12Compact.HistoricalOwnership.Queries.query2010_certified,N12Compact.HistoricalOwnership.Queries.query2011_certified,N12Compact.HistoricalOwnership.Queries.query2012_certified,N12Compact.C979SharedSelections.selected669,N12Compact.HistoricalOwnership.Queries.query2013_certified,N12Compact.HistoricalOwnership.Queries.query2014_certified,N12Compact.HistoricalOwnership.Queries.query2015_certified,N12Compact.HistoricalOwnership.Queries.query2016_certified,N12Compact.HistoricalOwnership.Queries.query2017_certified,N12Compact.HistoricalOwnership.Queries.query2018_certified,N12Compact.HistoricalOwnership.Queries.query2019_certified]⟩
private def single979_6_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(512,1,{0}),(512,1,{1}),(512,1,{0,1}),(512,1,{2}),(512,1,{0,2}),(512,1,{1,2}),(512,1,{0,1,2}),(512,1,{3}),(512,1,{0,3}),(512,1,{1,3}),(512,1,{0,1,3}),(512,1,{2,3}),(512,1,{0,2,3}),(512,1,{1,2,3}),(512,1,{4}),(512,1,{0,4}),(512,1,{1,4}),(512,1,{0,1,4}),(512,1,{2,4}),(512,1,{0,2,4}),(512,1,{1,2,4}),(512,1,{3,4}),(512,1,{0,3,4}),(512,1,{1,3,4}),(512,1,{2,3,4}),(512,1,{0,5}),(512,1,{1,5}),(512,1,{0,1,5}),(512,1,{0,2,5}),(512,1,{1,2,5}),(512,1,{0,3,5}),(512,1,{1,3,5}),(512,1,{4,5}),(512,1,{0,4,5}),(512,1,{1,4,5}),(512,1,{2,4,5}),(512,1,{3,4,5}),(512,1,{0,6}),(512,1,{1,6}),(512,1,{0,1,6}),(512,1,{0,2,6}),(512,1,{1,2,6}),(512,1,{0,3,6}),(512,1,{1,3,6}),(512,1,{4,6}),(512,1,{0,4,6}),(512,1,{1,4,6}),(512,1,{2,4,6}),(512,1,{3,4,6}),(512,1,{0,5,6}),(512,1,{1,5,6}),(512,1,{4,5,6}),(512,1,{7}),(512,1,{0,7}),(512,1,{1,7}),(512,1,{0,1,7}),(512,1,{2,7}),(512,1,{0,2,7}),(512,1,{1,2,7}),(512,1,{3,7}),(512,1,{0,3,7}),(512,1,{1,3,7}),(512,1,{2,3,7}),(512,1,{4,7}),(512,1,{0,4,7}),(512,1,{1,4,7}),(512,1,{2,4,7}),(512,1,{3,4,7}),(512,1,{5,7}),(512,1,{0,5,7}),(512,1,{1,5,7}),(512,1,{2,5,7}),(512,1,{3,5,7}),(512,1,{4,5,7}),(512,1,{6,7}),(512,1,{0,6,7}),(512,1,{1,6,7}),(512,1,{2,6,7}),(512,1,{3,6,7}),(512,1,{4,6,7}),(512,1,{5,6,7}),(512,1,{0,8}),(512,1,{1,8}),(512,1,{0,1,8}),(512,1,{2,8}),(512,1,{0,2,8}),(512,1,{1,2,8}),(512,1,{3,8}),(512,1,{0,3,8}),(512,1,{1,3,8}),(512,1,{2,3,8}),(512,1,{4,8}),(512,1,{0,4,8}),(512,1,{1,4,8}),(512,1,{2,4,8}),(512,1,{3,4,8}),(512,1,{0,5,8}),(512,1,{1,5,8}),(512,1,{4,5,8}),(512,1,{0,6,8}),(512,1,{1,6,8}),(512,1,{4,6,8}),(512,1,{7,8}),(512,1,{0,7,8}),(512,1,{1,7,8}),(512,1,{2,7,8}),(512,1,{3,7,8}),(512,1,{4,7,8}),(512,1,{5,7,8}),(512,1,{6,7,8}),(512,1,{9}),(512,1,{0,9}),(512,1,{1,9}),(512,1,{0,1,9}),(512,1,{2,9}),(512,1,{0,2,9}),(512,1,{1,2,9}),(512,1,{3,9}),(512,1,{0,3,9}),(512,1,{1,3,9}),(512,1,{2,3,9}),(512,1,{4,9}),(512,1,{0,4,9}),(512,1,{1,4,9}),(512,1,{2,4,9}),(512,1,{3,4,9}),(512,1,{5,9}),(512,1,{0,5,9}),(512,1,{1,5,9}),(512,1,{2,5,9}),(512,1,{3,5,9}),(512,1,{4,5,9}),(512,1,{0,6,9}),(512,1,{1,6,9}),(512,1,{2,6,9}),(512,1,{3,6,9}),(512,1,{4,6,9}),(512,1,{5,6,9}),(512,1,{7,9}),(512,1,{0,7,9}),(512,1,{1,7,9}),(512,1,{2,7,9}),(512,1,{3,7,9}),(512,1,{4,7,9}),(512,1,{5,7,9}),(512,1,{6,7,9}),(512,1,{8,9}),(512,1,{0,8,9}),(512,1,{1,8,9}),(512,1,{2,8,9}),(512,1,{3,8,9}),(512,1,{4,8,9}),(512,1,{5,8,9}),(512,1,{7,8,9})]
private theorem single979_6_1_queries_exact :
    single979_6_1Signatures = single979_6_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_6_1_queries_exact

private def single979_6_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{5},{2,5},{3,5},{2,3,5},{6},{2,6},{3,6},{2,3,6},{5,6},{2,5,6},{3,5,6},{8},{5,8},{2,5,8},{3,5,8},{6,8},{2,6,8},{3,6,8},{5,6,8},{6,9},{6,8,9}] : List (Finset Nat)) ∨ (512,1,owned) ∈ single979_6_1Signatures

private instance : DecidablePred single979_6_1_owned_claim := fun index => by
  unfold single979_6_1_owned_claim
  infer_instance

private theorem single979_6_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_6_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_6_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_6_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_6_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_6_1 case979Family 1 single979_6_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨512,1,3,[{5},{2,5},{3,5},{2,3,5},{6},{2,6},{3,6},{2,3,6},{5,6},{2,5,6},{3,5,6},{8},{5,8},{2,5,8},{3,5,8},{6,8},{2,6,8},{3,6,8},{5,6,8},{6,9},{6,8,9}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_6_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_6_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_6_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_6_1_owned_block0
      · exact single979_6_1_owned_block1
      · exact single979_6_1_owned_block2
      · exact single979_6_1_owned_block3
      · exact single979_6_1_owned_block4
      · exact single979_6_1_owned_block5
      · exact single979_6_1_owned_block6
      · exact single979_6_1_owned_block7
      · exact single979_6_1_owned_block8
      · exact single979_6_1_owned_block9
      · exact single979_6_1_owned_block10
      · exact single979_6_1_owned_block11
      · exact single979_6_1_owned_block12
      · exact single979_6_1_owned_block13
      · exact single979_6_1_owned_block14
      · exact single979_6_1_owned_block15
      · exact single979_6_1_owned_block16
      · exact single979_6_1_owned_block17
      · exact single979_6_1_owned_block18
      · exact single979_6_1_owned_block19
      · exact single979_6_1_owned_block20
      · exact single979_6_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_6_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_6_1_metadata

theorem single979_6_1_checked : single979_6_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_6_1 case979Family 1
    single979_6_1Signatures single979_6_1_queries_exact (by decide) single979_6_1_metadata

end
end S12

import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_8_1 : DirectSingleDomain := ⟨4096,1,3,[{0},{1},{0,1},{3},{0,3},{1,3},{0,1,3}],[N12Compact.C979SharedSelections.selected1039,N12Compact.C979SharedSelections.selected1040,N12Compact.C979SharedSelections.selected1041,N12Compact.HistoricalOwnership.Queries.query900_certified,N12Compact.C979SharedSelections.selected1042,N12Compact.HistoricalOwnership.Queries.query901_certified,N12Compact.HistoricalOwnership.Queries.query902_certified,N12Compact.C979SharedSelections.selected1043,N12Compact.C979SharedSelections.selected1044,N12Compact.C979SharedSelections.selected1045,N12Compact.HistoricalOwnership.Queries.query903_certified,N12Compact.C979SharedSelections.selected1046,N12Compact.HistoricalOwnership.Queries.query904_certified,N12Compact.HistoricalOwnership.Queries.query905_certified,N12Compact.C979SharedSelections.selected1047,N12Compact.HistoricalOwnership.Queries.query906_certified,N12Compact.HistoricalOwnership.Queries.query907_certified,N12Compact.HistoricalOwnership.Queries.query908_certified,N12Compact.C979SharedSelections.selected1048,N12Compact.C979SharedSelections.selected1049,N12Compact.C979SharedSelections.selected1050,N12Compact.HistoricalOwnership.Queries.query909_certified,N12Compact.C979SharedSelections.selected1051,N12Compact.HistoricalOwnership.Queries.query910_certified,N12Compact.HistoricalOwnership.Queries.query911_certified,N12Compact.C979SharedSelections.selected1052,N12Compact.HistoricalOwnership.Queries.query912_certified,N12Compact.HistoricalOwnership.Queries.query913_certified,N12Compact.HistoricalOwnership.Queries.query914_certified,N12Compact.C979SharedSelections.selected1053,N12Compact.HistoricalOwnership.Queries.query915_certified,N12Compact.HistoricalOwnership.Queries.query916_certified,N12Compact.HistoricalOwnership.Queries.query917_certified,N12Compact.HistoricalOwnership.Queries.query918_certified,N12Compact.C979SharedSelections.selected1054,N12Compact.C979SharedSelections.selected1055,N12Compact.C979SharedSelections.selected1056,N12Compact.HistoricalOwnership.Queries.query919_certified,N12Compact.C979SharedSelections.selected1057,N12Compact.HistoricalOwnership.Queries.query920_certified,N12Compact.HistoricalOwnership.Queries.query921_certified,N12Compact.C979SharedSelections.selected1058,N12Compact.HistoricalOwnership.Queries.query922_certified,N12Compact.HistoricalOwnership.Queries.query923_certified,N12Compact.HistoricalOwnership.Queries.query924_certified,N12Compact.C979SharedSelections.selected1059,N12Compact.HistoricalOwnership.Queries.query925_certified,N12Compact.HistoricalOwnership.Queries.query926_certified,N12Compact.HistoricalOwnership.Queries.query927_certified,N12Compact.HistoricalOwnership.Queries.query928_certified,N12Compact.C979SharedSelections.selected1060,N12Compact.HistoricalOwnership.Queries.query929_certified,N12Compact.HistoricalOwnership.Queries.query930_certified,N12Compact.HistoricalOwnership.Queries.query931_certified,N12Compact.HistoricalOwnership.Queries.query932_certified,N12Compact.HistoricalOwnership.Queries.query933_certified,N12Compact.C979SharedSelections.selected1061,N12Compact.C979SharedSelections.selected1062,N12Compact.C979SharedSelections.selected1063,N12Compact.HistoricalOwnership.Queries.query934_certified,N12Compact.C979SharedSelections.selected1064,N12Compact.HistoricalOwnership.Queries.query935_certified,N12Compact.HistoricalOwnership.Queries.query936_certified,N12Compact.C979SharedSelections.selected1065,N12Compact.HistoricalOwnership.Queries.query937_certified,N12Compact.HistoricalOwnership.Queries.query938_certified,N12Compact.HistoricalOwnership.Queries.query939_certified,N12Compact.C979SharedSelections.selected1066,N12Compact.HistoricalOwnership.Queries.query940_certified,N12Compact.HistoricalOwnership.Queries.query941_certified,N12Compact.HistoricalOwnership.Queries.query942_certified,N12Compact.HistoricalOwnership.Queries.query943_certified,N12Compact.C979SharedSelections.selected1067,N12Compact.HistoricalOwnership.Queries.query944_certified,N12Compact.HistoricalOwnership.Queries.query945_certified,N12Compact.HistoricalOwnership.Queries.query946_certified,N12Compact.HistoricalOwnership.Queries.query947_certified,N12Compact.HistoricalOwnership.Queries.query948_certified,N12Compact.C979SharedSelections.selected1068,N12Compact.HistoricalOwnership.Queries.query949_certified,N12Compact.HistoricalOwnership.Queries.query950_certified,N12Compact.HistoricalOwnership.Queries.query951_certified,N12Compact.HistoricalOwnership.Queries.query952_certified,N12Compact.HistoricalOwnership.Queries.query953_certified,N12Compact.HistoricalOwnership.Queries.query954_certified,N12Compact.C979SharedSelections.selected1069,N12Compact.C979SharedSelections.selected1070,N12Compact.C979SharedSelections.selected1071,N12Compact.HistoricalOwnership.Queries.query955_certified,N12Compact.C979SharedSelections.selected1072,N12Compact.HistoricalOwnership.Queries.query956_certified,N12Compact.HistoricalOwnership.Queries.query957_certified,N12Compact.C979SharedSelections.selected1073,N12Compact.HistoricalOwnership.Queries.query958_certified,N12Compact.HistoricalOwnership.Queries.query959_certified,N12Compact.HistoricalOwnership.Queries.query960_certified,N12Compact.C979SharedSelections.selected1074,N12Compact.HistoricalOwnership.Queries.query961_certified,N12Compact.HistoricalOwnership.Queries.query962_certified,N12Compact.HistoricalOwnership.Queries.query963_certified,N12Compact.HistoricalOwnership.Queries.query964_certified,N12Compact.C979SharedSelections.selected1075,N12Compact.HistoricalOwnership.Queries.query965_certified,N12Compact.HistoricalOwnership.Queries.query966_certified,N12Compact.HistoricalOwnership.Queries.query967_certified,N12Compact.HistoricalOwnership.Queries.query968_certified,N12Compact.HistoricalOwnership.Queries.query969_certified,N12Compact.C979SharedSelections.selected1076,N12Compact.HistoricalOwnership.Queries.query970_certified,N12Compact.HistoricalOwnership.Queries.query971_certified,N12Compact.HistoricalOwnership.Queries.query972_certified,N12Compact.HistoricalOwnership.Queries.query973_certified,N12Compact.HistoricalOwnership.Queries.query974_certified,N12Compact.HistoricalOwnership.Queries.query975_certified,N12Compact.C979SharedSelections.selected1077,N12Compact.HistoricalOwnership.Queries.query976_certified,N12Compact.HistoricalOwnership.Queries.query977_certified,N12Compact.HistoricalOwnership.Queries.query978_certified,N12Compact.HistoricalOwnership.Queries.query979_certified,N12Compact.HistoricalOwnership.Queries.query980_certified,N12Compact.HistoricalOwnership.Queries.query981_certified,N12Compact.HistoricalOwnership.Queries.query982_certified,N12Compact.C979SharedSelections.selected1078,N12Compact.C979SharedSelections.selected1079,N12Compact.C979SharedSelections.selected1080,N12Compact.HistoricalOwnership.Queries.query983_certified,N12Compact.C979SharedSelections.selected1081,N12Compact.HistoricalOwnership.Queries.query984_certified,N12Compact.HistoricalOwnership.Queries.query985_certified,N12Compact.C979SharedSelections.selected1082,N12Compact.HistoricalOwnership.Queries.query986_certified,N12Compact.HistoricalOwnership.Queries.query987_certified,N12Compact.HistoricalOwnership.Queries.query988_certified,N12Compact.C979SharedSelections.selected1083,N12Compact.HistoricalOwnership.Queries.query989_certified,N12Compact.HistoricalOwnership.Queries.query990_certified,N12Compact.HistoricalOwnership.Queries.query991_certified,N12Compact.HistoricalOwnership.Queries.query992_certified,N12Compact.C979SharedSelections.selected1084,N12Compact.HistoricalOwnership.Queries.query993_certified,N12Compact.HistoricalOwnership.Queries.query994_certified,N12Compact.HistoricalOwnership.Queries.query995_certified,N12Compact.HistoricalOwnership.Queries.query996_certified,N12Compact.HistoricalOwnership.Queries.query997_certified,N12Compact.C979SharedSelections.selected1085,N12Compact.HistoricalOwnership.Queries.query998_certified,N12Compact.HistoricalOwnership.Queries.query999_certified,N12Compact.HistoricalOwnership.Queries.query1000_certified,N12Compact.HistoricalOwnership.Queries.query1001_certified,N12Compact.HistoricalOwnership.Queries.query1002_certified,N12Compact.HistoricalOwnership.Queries.query1003_certified,N12Compact.C979SharedSelections.selected1086,N12Compact.HistoricalOwnership.Queries.query1004_certified,N12Compact.HistoricalOwnership.Queries.query1005_certified,N12Compact.HistoricalOwnership.Queries.query1006_certified,N12Compact.HistoricalOwnership.Queries.query1007_certified,N12Compact.HistoricalOwnership.Queries.query1008_certified,N12Compact.HistoricalOwnership.Queries.query1009_certified,N12Compact.HistoricalOwnership.Queries.query1010_certified,N12Compact.C979SharedSelections.selected1087,N12Compact.HistoricalOwnership.Queries.query1011_certified,N12Compact.HistoricalOwnership.Queries.query1012_certified,N12Compact.HistoricalOwnership.Queries.query1013_certified,N12Compact.HistoricalOwnership.Queries.query1014_certified,N12Compact.HistoricalOwnership.Queries.query1015_certified,N12Compact.HistoricalOwnership.Queries.query1016_certified,N12Compact.HistoricalOwnership.Queries.query1017_certified,N12Compact.HistoricalOwnership.Queries.query1018_certified]⟩
private def single979_8_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(4096,1,{2}),(4096,1,{0,2}),(4096,1,{1,2}),(4096,1,{0,1,2}),(4096,1,{2,3}),(4096,1,{0,2,3}),(4096,1,{1,2,3}),(4096,1,{4}),(4096,1,{0,4}),(4096,1,{1,4}),(4096,1,{0,1,4}),(4096,1,{2,4}),(4096,1,{0,2,4}),(4096,1,{1,2,4}),(4096,1,{3,4}),(4096,1,{0,3,4}),(4096,1,{1,3,4}),(4096,1,{2,3,4}),(4096,1,{5}),(4096,1,{0,5}),(4096,1,{1,5}),(4096,1,{0,1,5}),(4096,1,{2,5}),(4096,1,{0,2,5}),(4096,1,{1,2,5}),(4096,1,{3,5}),(4096,1,{0,3,5}),(4096,1,{1,3,5}),(4096,1,{2,3,5}),(4096,1,{4,5}),(4096,1,{0,4,5}),(4096,1,{1,4,5}),(4096,1,{2,4,5}),(4096,1,{3,4,5}),(4096,1,{6}),(4096,1,{0,6}),(4096,1,{1,6}),(4096,1,{0,1,6}),(4096,1,{2,6}),(4096,1,{0,2,6}),(4096,1,{1,2,6}),(4096,1,{3,6}),(4096,1,{0,3,6}),(4096,1,{1,3,6}),(4096,1,{2,3,6}),(4096,1,{4,6}),(4096,1,{0,4,6}),(4096,1,{1,4,6}),(4096,1,{2,4,6}),(4096,1,{3,4,6}),(4096,1,{5,6}),(4096,1,{0,5,6}),(4096,1,{1,5,6}),(4096,1,{2,5,6}),(4096,1,{3,5,6}),(4096,1,{4,5,6}),(4096,1,{7}),(4096,1,{0,7}),(4096,1,{1,7}),(4096,1,{0,1,7}),(4096,1,{2,7}),(4096,1,{0,2,7}),(4096,1,{1,2,7}),(4096,1,{3,7}),(4096,1,{0,3,7}),(4096,1,{1,3,7}),(4096,1,{2,3,7}),(4096,1,{4,7}),(4096,1,{0,4,7}),(4096,1,{1,4,7}),(4096,1,{2,4,7}),(4096,1,{3,4,7}),(4096,1,{5,7}),(4096,1,{0,5,7}),(4096,1,{1,5,7}),(4096,1,{2,5,7}),(4096,1,{3,5,7}),(4096,1,{4,5,7}),(4096,1,{6,7}),(4096,1,{0,6,7}),(4096,1,{1,6,7}),(4096,1,{2,6,7}),(4096,1,{3,6,7}),(4096,1,{4,6,7}),(4096,1,{5,6,7}),(4096,1,{8}),(4096,1,{0,8}),(4096,1,{1,8}),(4096,1,{0,1,8}),(4096,1,{2,8}),(4096,1,{0,2,8}),(4096,1,{1,2,8}),(4096,1,{3,8}),(4096,1,{0,3,8}),(4096,1,{1,3,8}),(4096,1,{2,3,8}),(4096,1,{4,8}),(4096,1,{0,4,8}),(4096,1,{1,4,8}),(4096,1,{2,4,8}),(4096,1,{3,4,8}),(4096,1,{5,8}),(4096,1,{0,5,8}),(4096,1,{1,5,8}),(4096,1,{2,5,8}),(4096,1,{3,5,8}),(4096,1,{4,5,8}),(4096,1,{6,8}),(4096,1,{0,6,8}),(4096,1,{1,6,8}),(4096,1,{2,6,8}),(4096,1,{3,6,8}),(4096,1,{4,6,8}),(4096,1,{5,6,8}),(4096,1,{7,8}),(4096,1,{0,7,8}),(4096,1,{1,7,8}),(4096,1,{2,7,8}),(4096,1,{3,7,8}),(4096,1,{4,7,8}),(4096,1,{5,7,8}),(4096,1,{6,7,8}),(4096,1,{9}),(4096,1,{0,9}),(4096,1,{1,9}),(4096,1,{0,1,9}),(4096,1,{2,9}),(4096,1,{0,2,9}),(4096,1,{1,2,9}),(4096,1,{3,9}),(4096,1,{0,3,9}),(4096,1,{1,3,9}),(4096,1,{2,3,9}),(4096,1,{4,9}),(4096,1,{0,4,9}),(4096,1,{1,4,9}),(4096,1,{2,4,9}),(4096,1,{3,4,9}),(4096,1,{5,9}),(4096,1,{0,5,9}),(4096,1,{1,5,9}),(4096,1,{2,5,9}),(4096,1,{3,5,9}),(4096,1,{4,5,9}),(4096,1,{6,9}),(4096,1,{0,6,9}),(4096,1,{1,6,9}),(4096,1,{2,6,9}),(4096,1,{3,6,9}),(4096,1,{4,6,9}),(4096,1,{5,6,9}),(4096,1,{7,9}),(4096,1,{0,7,9}),(4096,1,{1,7,9}),(4096,1,{2,7,9}),(4096,1,{3,7,9}),(4096,1,{4,7,9}),(4096,1,{5,7,9}),(4096,1,{6,7,9}),(4096,1,{8,9}),(4096,1,{0,8,9}),(4096,1,{1,8,9}),(4096,1,{2,8,9}),(4096,1,{3,8,9}),(4096,1,{4,8,9}),(4096,1,{5,8,9}),(4096,1,{6,8,9}),(4096,1,{7,8,9})]
private theorem single979_8_1_queries_exact :
    single979_8_1Signatures = single979_8_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_8_1_queries_exact

private def single979_8_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{0},{1},{0,1},{3},{0,3},{1,3},{0,1,3}] : List (Finset Nat)) ∨ (4096,1,owned) ∈ single979_8_1Signatures

private instance : DecidablePred single979_8_1_owned_claim := fun index => by
  unfold single979_8_1_owned_claim
  infer_instance

private theorem single979_8_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_8_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_8_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_8_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_8_1 case979Family 1 single979_8_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨4096,1,3,[{0},{1},{0,1},{3},{0,3},{1,3},{0,1,3}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_8_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_8_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_8_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_8_1_owned_block0
      · exact single979_8_1_owned_block1
      · exact single979_8_1_owned_block2
      · exact single979_8_1_owned_block3
      · exact single979_8_1_owned_block4
      · exact single979_8_1_owned_block5
      · exact single979_8_1_owned_block6
      · exact single979_8_1_owned_block7
      · exact single979_8_1_owned_block8
      · exact single979_8_1_owned_block9
      · exact single979_8_1_owned_block10
      · exact single979_8_1_owned_block11
      · exact single979_8_1_owned_block12
      · exact single979_8_1_owned_block13
      · exact single979_8_1_owned_block14
      · exact single979_8_1_owned_block15
      · exact single979_8_1_owned_block16
      · exact single979_8_1_owned_block17
      · exact single979_8_1_owned_block18
      · exact single979_8_1_owned_block19
      · exact single979_8_1_owned_block20
      · exact single979_8_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_8_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_8_1_metadata

theorem single979_8_1_checked : single979_8_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_8_1 case979Family 1
    single979_8_1Signatures single979_8_1_queries_exact (by decide) single979_8_1_metadata

end
end S12

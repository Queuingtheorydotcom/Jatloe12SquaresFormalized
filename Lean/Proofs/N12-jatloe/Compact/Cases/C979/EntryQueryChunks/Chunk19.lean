import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_9_1 : DirectSingleDomain := ⟨8192,1,3,[{2},{0,2},{5},{2,5},{0,2,5},{5,8},{2,5,8}],[N12Compact.C979SharedSelections.selected1194,N12Compact.C979SharedSelections.selected1195,N12Compact.C979SharedSelections.selected1196,N12Compact.C979SharedSelections.selected1197,N12Compact.HistoricalOwnership.Queries.query1021_certified,N12Compact.C979SharedSelections.selected1198,N12Compact.C979SharedSelections.selected1199,N12Compact.C979SharedSelections.selected1200,N12Compact.HistoricalOwnership.Queries.query1022_certified,N12Compact.C979SharedSelections.selected1201,N12Compact.HistoricalOwnership.Queries.query1023_certified,N12Compact.HistoricalOwnership.Queries.query1024_certified,N12Compact.C979SharedSelections.selected1202,N12Compact.C979SharedSelections.selected1203,N12Compact.C979SharedSelections.selected1204,N12Compact.HistoricalOwnership.Queries.query1025_certified,N12Compact.C979SharedSelections.selected1205,N12Compact.HistoricalOwnership.Queries.query1026_certified,N12Compact.HistoricalOwnership.Queries.query1027_certified,N12Compact.C979SharedSelections.selected1206,N12Compact.HistoricalOwnership.Queries.query1028_certified,N12Compact.HistoricalOwnership.Queries.query1029_certified,N12Compact.HistoricalOwnership.Queries.query1030_certified,N12Compact.C979SharedSelections.selected1207,N12Compact.C979SharedSelections.selected1208,N12Compact.HistoricalOwnership.Queries.query1031_certified,N12Compact.HistoricalOwnership.Queries.query1032_certified,N12Compact.C979SharedSelections.selected1209,N12Compact.HistoricalOwnership.Queries.query1033_certified,N12Compact.HistoricalOwnership.Queries.query1034_certified,N12Compact.HistoricalOwnership.Queries.query1035_certified,N12Compact.C979SharedSelections.selected1210,N12Compact.HistoricalOwnership.Queries.query1036_certified,N12Compact.HistoricalOwnership.Queries.query1037_certified,N12Compact.HistoricalOwnership.Queries.query1038_certified,N12Compact.HistoricalOwnership.Queries.query1039_certified,N12Compact.C979SharedSelections.selected1211,N12Compact.C979SharedSelections.selected1212,N12Compact.C979SharedSelections.selected1213,N12Compact.HistoricalOwnership.Queries.query1040_certified,N12Compact.C979SharedSelections.selected1214,N12Compact.HistoricalOwnership.Queries.query1041_certified,N12Compact.HistoricalOwnership.Queries.query1042_certified,N12Compact.C979SharedSelections.selected1215,N12Compact.HistoricalOwnership.Queries.query1043_certified,N12Compact.HistoricalOwnership.Queries.query1044_certified,N12Compact.HistoricalOwnership.Queries.query1045_certified,N12Compact.C979SharedSelections.selected1216,N12Compact.HistoricalOwnership.Queries.query1046_certified,N12Compact.HistoricalOwnership.Queries.query1047_certified,N12Compact.HistoricalOwnership.Queries.query1048_certified,N12Compact.HistoricalOwnership.Queries.query1049_certified,N12Compact.C979SharedSelections.selected1217,N12Compact.HistoricalOwnership.Queries.query1050_certified,N12Compact.HistoricalOwnership.Queries.query1051_certified,N12Compact.HistoricalOwnership.Queries.query1052_certified,N12Compact.HistoricalOwnership.Queries.query1053_certified,N12Compact.HistoricalOwnership.Queries.query1054_certified,N12Compact.C979SharedSelections.selected1218,N12Compact.C979SharedSelections.selected1219,N12Compact.C979SharedSelections.selected1220,N12Compact.HistoricalOwnership.Queries.query1055_certified,N12Compact.C979SharedSelections.selected1221,N12Compact.HistoricalOwnership.Queries.query1056_certified,N12Compact.HistoricalOwnership.Queries.query1057_certified,N12Compact.C979SharedSelections.selected1222,N12Compact.HistoricalOwnership.Queries.query1058_certified,N12Compact.HistoricalOwnership.Queries.query1059_certified,N12Compact.HistoricalOwnership.Queries.query1060_certified,N12Compact.C979SharedSelections.selected1223,N12Compact.HistoricalOwnership.Queries.query1061_certified,N12Compact.HistoricalOwnership.Queries.query1062_certified,N12Compact.HistoricalOwnership.Queries.query1063_certified,N12Compact.HistoricalOwnership.Queries.query1064_certified,N12Compact.C979SharedSelections.selected1224,N12Compact.HistoricalOwnership.Queries.query1065_certified,N12Compact.HistoricalOwnership.Queries.query1066_certified,N12Compact.HistoricalOwnership.Queries.query1067_certified,N12Compact.HistoricalOwnership.Queries.query1068_certified,N12Compact.HistoricalOwnership.Queries.query1069_certified,N12Compact.C979SharedSelections.selected1225,N12Compact.HistoricalOwnership.Queries.query1070_certified,N12Compact.HistoricalOwnership.Queries.query1071_certified,N12Compact.HistoricalOwnership.Queries.query1072_certified,N12Compact.HistoricalOwnership.Queries.query1073_certified,N12Compact.HistoricalOwnership.Queries.query1074_certified,N12Compact.HistoricalOwnership.Queries.query1075_certified,N12Compact.C979SharedSelections.selected1226,N12Compact.C979SharedSelections.selected1227,N12Compact.C979SharedSelections.selected1228,N12Compact.HistoricalOwnership.Queries.query1076_certified,N12Compact.C979SharedSelections.selected1229,N12Compact.HistoricalOwnership.Queries.query1077_certified,N12Compact.HistoricalOwnership.Queries.query1078_certified,N12Compact.C979SharedSelections.selected1230,N12Compact.HistoricalOwnership.Queries.query1079_certified,N12Compact.HistoricalOwnership.Queries.query1080_certified,N12Compact.HistoricalOwnership.Queries.query1081_certified,N12Compact.C979SharedSelections.selected1231,N12Compact.HistoricalOwnership.Queries.query1082_certified,N12Compact.HistoricalOwnership.Queries.query1083_certified,N12Compact.HistoricalOwnership.Queries.query1084_certified,N12Compact.HistoricalOwnership.Queries.query1085_certified,N12Compact.HistoricalOwnership.Queries.query1086_certified,N12Compact.HistoricalOwnership.Queries.query1087_certified,N12Compact.HistoricalOwnership.Queries.query1088_certified,N12Compact.HistoricalOwnership.Queries.query1089_certified,N12Compact.C979SharedSelections.selected1232,N12Compact.HistoricalOwnership.Queries.query1090_certified,N12Compact.HistoricalOwnership.Queries.query1091_certified,N12Compact.HistoricalOwnership.Queries.query1092_certified,N12Compact.HistoricalOwnership.Queries.query1093_certified,N12Compact.HistoricalOwnership.Queries.query1094_certified,N12Compact.HistoricalOwnership.Queries.query1095_certified,N12Compact.C979SharedSelections.selected1233,N12Compact.HistoricalOwnership.Queries.query1096_certified,N12Compact.HistoricalOwnership.Queries.query1097_certified,N12Compact.HistoricalOwnership.Queries.query1098_certified,N12Compact.HistoricalOwnership.Queries.query1099_certified,N12Compact.HistoricalOwnership.Queries.query1100_certified,N12Compact.HistoricalOwnership.Queries.query1101_certified,N12Compact.HistoricalOwnership.Queries.query1102_certified,N12Compact.C979SharedSelections.selected1234,N12Compact.C979SharedSelections.selected1235,N12Compact.C979SharedSelections.selected1236,N12Compact.HistoricalOwnership.Queries.query1103_certified,N12Compact.C979SharedSelections.selected1237,N12Compact.HistoricalOwnership.Queries.query1104_certified,N12Compact.HistoricalOwnership.Queries.query1105_certified,N12Compact.C979SharedSelections.selected1238,N12Compact.HistoricalOwnership.Queries.query1106_certified,N12Compact.HistoricalOwnership.Queries.query1107_certified,N12Compact.HistoricalOwnership.Queries.query1108_certified,N12Compact.C979SharedSelections.selected1239,N12Compact.HistoricalOwnership.Queries.query1109_certified,N12Compact.HistoricalOwnership.Queries.query1110_certified,N12Compact.HistoricalOwnership.Queries.query1111_certified,N12Compact.HistoricalOwnership.Queries.query1112_certified,N12Compact.C979SharedSelections.selected1240,N12Compact.HistoricalOwnership.Queries.query1113_certified,N12Compact.HistoricalOwnership.Queries.query1114_certified,N12Compact.HistoricalOwnership.Queries.query1115_certified,N12Compact.HistoricalOwnership.Queries.query1116_certified,N12Compact.HistoricalOwnership.Queries.query1117_certified,N12Compact.C979SharedSelections.selected1241,N12Compact.HistoricalOwnership.Queries.query1118_certified,N12Compact.HistoricalOwnership.Queries.query1119_certified,N12Compact.HistoricalOwnership.Queries.query1120_certified,N12Compact.HistoricalOwnership.Queries.query1121_certified,N12Compact.HistoricalOwnership.Queries.query1122_certified,N12Compact.HistoricalOwnership.Queries.query1123_certified,N12Compact.C979SharedSelections.selected1242,N12Compact.HistoricalOwnership.Queries.query1124_certified,N12Compact.HistoricalOwnership.Queries.query1125_certified,N12Compact.HistoricalOwnership.Queries.query1126_certified,N12Compact.HistoricalOwnership.Queries.query1127_certified,N12Compact.HistoricalOwnership.Queries.query1128_certified,N12Compact.HistoricalOwnership.Queries.query1129_certified,N12Compact.HistoricalOwnership.Queries.query1130_certified,N12Compact.C979SharedSelections.selected1243,N12Compact.HistoricalOwnership.Queries.query1131_certified,N12Compact.HistoricalOwnership.Queries.query1132_certified,N12Compact.HistoricalOwnership.Queries.query1133_certified,N12Compact.HistoricalOwnership.Queries.query1134_certified,N12Compact.HistoricalOwnership.Queries.query1135_certified,N12Compact.HistoricalOwnership.Queries.query1136_certified,N12Compact.HistoricalOwnership.Queries.query1137_certified,N12Compact.HistoricalOwnership.Queries.query1138_certified]⟩
private def single979_9_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(8192,1,{0}),(8192,1,{1}),(8192,1,{0,1}),(8192,1,{1,2}),(8192,1,{0,1,2}),(8192,1,{3}),(8192,1,{0,3}),(8192,1,{1,3}),(8192,1,{0,1,3}),(8192,1,{2,3}),(8192,1,{0,2,3}),(8192,1,{1,2,3}),(8192,1,{4}),(8192,1,{0,4}),(8192,1,{1,4}),(8192,1,{0,1,4}),(8192,1,{2,4}),(8192,1,{0,2,4}),(8192,1,{1,2,4}),(8192,1,{3,4}),(8192,1,{0,3,4}),(8192,1,{1,3,4}),(8192,1,{2,3,4}),(8192,1,{0,5}),(8192,1,{1,5}),(8192,1,{0,1,5}),(8192,1,{1,2,5}),(8192,1,{3,5}),(8192,1,{0,3,5}),(8192,1,{1,3,5}),(8192,1,{2,3,5}),(8192,1,{4,5}),(8192,1,{0,4,5}),(8192,1,{1,4,5}),(8192,1,{2,4,5}),(8192,1,{3,4,5}),(8192,1,{6}),(8192,1,{0,6}),(8192,1,{1,6}),(8192,1,{0,1,6}),(8192,1,{2,6}),(8192,1,{0,2,6}),(8192,1,{1,2,6}),(8192,1,{3,6}),(8192,1,{0,3,6}),(8192,1,{1,3,6}),(8192,1,{2,3,6}),(8192,1,{4,6}),(8192,1,{0,4,6}),(8192,1,{1,4,6}),(8192,1,{2,4,6}),(8192,1,{3,4,6}),(8192,1,{5,6}),(8192,1,{0,5,6}),(8192,1,{1,5,6}),(8192,1,{2,5,6}),(8192,1,{3,5,6}),(8192,1,{4,5,6}),(8192,1,{7}),(8192,1,{0,7}),(8192,1,{1,7}),(8192,1,{0,1,7}),(8192,1,{2,7}),(8192,1,{0,2,7}),(8192,1,{1,2,7}),(8192,1,{3,7}),(8192,1,{0,3,7}),(8192,1,{1,3,7}),(8192,1,{2,3,7}),(8192,1,{4,7}),(8192,1,{0,4,7}),(8192,1,{1,4,7}),(8192,1,{2,4,7}),(8192,1,{3,4,7}),(8192,1,{5,7}),(8192,1,{0,5,7}),(8192,1,{1,5,7}),(8192,1,{2,5,7}),(8192,1,{3,5,7}),(8192,1,{4,5,7}),(8192,1,{6,7}),(8192,1,{0,6,7}),(8192,1,{1,6,7}),(8192,1,{2,6,7}),(8192,1,{3,6,7}),(8192,1,{4,6,7}),(8192,1,{5,6,7}),(8192,1,{8}),(8192,1,{0,8}),(8192,1,{1,8}),(8192,1,{0,1,8}),(8192,1,{2,8}),(8192,1,{0,2,8}),(8192,1,{1,2,8}),(8192,1,{3,8}),(8192,1,{0,3,8}),(8192,1,{1,3,8}),(8192,1,{2,3,8}),(8192,1,{4,8}),(8192,1,{0,4,8}),(8192,1,{1,4,8}),(8192,1,{2,4,8}),(8192,1,{3,4,8}),(8192,1,{0,5,8}),(8192,1,{1,5,8}),(8192,1,{3,5,8}),(8192,1,{4,5,8}),(8192,1,{6,8}),(8192,1,{0,6,8}),(8192,1,{1,6,8}),(8192,1,{2,6,8}),(8192,1,{3,6,8}),(8192,1,{4,6,8}),(8192,1,{5,6,8}),(8192,1,{7,8}),(8192,1,{0,7,8}),(8192,1,{1,7,8}),(8192,1,{2,7,8}),(8192,1,{3,7,8}),(8192,1,{4,7,8}),(8192,1,{5,7,8}),(8192,1,{6,7,8}),(8192,1,{9}),(8192,1,{0,9}),(8192,1,{1,9}),(8192,1,{0,1,9}),(8192,1,{2,9}),(8192,1,{0,2,9}),(8192,1,{1,2,9}),(8192,1,{3,9}),(8192,1,{0,3,9}),(8192,1,{1,3,9}),(8192,1,{2,3,9}),(8192,1,{4,9}),(8192,1,{0,4,9}),(8192,1,{1,4,9}),(8192,1,{2,4,9}),(8192,1,{3,4,9}),(8192,1,{5,9}),(8192,1,{0,5,9}),(8192,1,{1,5,9}),(8192,1,{2,5,9}),(8192,1,{3,5,9}),(8192,1,{4,5,9}),(8192,1,{6,9}),(8192,1,{0,6,9}),(8192,1,{1,6,9}),(8192,1,{2,6,9}),(8192,1,{3,6,9}),(8192,1,{4,6,9}),(8192,1,{5,6,9}),(8192,1,{7,9}),(8192,1,{0,7,9}),(8192,1,{1,7,9}),(8192,1,{2,7,9}),(8192,1,{3,7,9}),(8192,1,{4,7,9}),(8192,1,{5,7,9}),(8192,1,{6,7,9}),(8192,1,{8,9}),(8192,1,{0,8,9}),(8192,1,{1,8,9}),(8192,1,{2,8,9}),(8192,1,{3,8,9}),(8192,1,{4,8,9}),(8192,1,{5,8,9}),(8192,1,{6,8,9}),(8192,1,{7,8,9})]
private theorem single979_9_1_queries_exact :
    single979_9_1Signatures = single979_9_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_9_1_queries_exact

private def single979_9_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{2},{0,2},{5},{2,5},{0,2,5},{5,8},{2,5,8}] : List (Finset Nat)) ∨ (8192,1,owned) ∈ single979_9_1Signatures

private instance : DecidablePred single979_9_1_owned_claim := fun index => by
  unfold single979_9_1_owned_claim
  infer_instance

private theorem single979_9_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_9_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_9_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_9_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_9_1 case979Family 1 single979_9_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨8192,1,3,[{2},{0,2},{5},{2,5},{0,2,5},{5,8},{2,5,8}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_9_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_9_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_9_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_9_1_owned_block0
      · exact single979_9_1_owned_block1
      · exact single979_9_1_owned_block2
      · exact single979_9_1_owned_block3
      · exact single979_9_1_owned_block4
      · exact single979_9_1_owned_block5
      · exact single979_9_1_owned_block6
      · exact single979_9_1_owned_block7
      · exact single979_9_1_owned_block8
      · exact single979_9_1_owned_block9
      · exact single979_9_1_owned_block10
      · exact single979_9_1_owned_block11
      · exact single979_9_1_owned_block12
      · exact single979_9_1_owned_block13
      · exact single979_9_1_owned_block14
      · exact single979_9_1_owned_block15
      · exact single979_9_1_owned_block16
      · exact single979_9_1_owned_block17
      · exact single979_9_1_owned_block18
      · exact single979_9_1_owned_block19
      · exact single979_9_1_owned_block20
      · exact single979_9_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_9_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_9_1_metadata

theorem single979_9_1_checked : single979_9_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_9_1 case979Family 1
    single979_9_1Signatures single979_9_1_queries_exact (by decide) single979_9_1_metadata

end
end S12

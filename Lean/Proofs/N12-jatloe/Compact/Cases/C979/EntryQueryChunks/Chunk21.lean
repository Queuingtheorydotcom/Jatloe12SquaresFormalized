import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_10_1 : DirectSingleDomain := ⟨16384,1,3,[{6},{8},{6,8},{9},{6,9},{8,9},{6,8,9}],[N12Compact.C979SharedSelections.selected1344,N12Compact.C979SharedSelections.selected1345,N12Compact.C979SharedSelections.selected1346,N12Compact.C979SharedSelections.selected1347,N12Compact.C979SharedSelections.selected1348,N12Compact.C979SharedSelections.selected1349,N12Compact.HistoricalOwnership.Queries.query1143_certified,N12Compact.C979SharedSelections.selected1350,N12Compact.C979SharedSelections.selected1351,N12Compact.C979SharedSelections.selected1352,N12Compact.HistoricalOwnership.Queries.query1144_certified,N12Compact.C979SharedSelections.selected1353,N12Compact.HistoricalOwnership.Queries.query1145_certified,N12Compact.HistoricalOwnership.Queries.query1146_certified,N12Compact.C979SharedSelections.selected1354,N12Compact.C979SharedSelections.selected1355,N12Compact.C979SharedSelections.selected1356,N12Compact.HistoricalOwnership.Queries.query1147_certified,N12Compact.C979SharedSelections.selected1357,N12Compact.HistoricalOwnership.Queries.query1148_certified,N12Compact.HistoricalOwnership.Queries.query1149_certified,N12Compact.C979SharedSelections.selected1358,N12Compact.HistoricalOwnership.Queries.query1150_certified,N12Compact.HistoricalOwnership.Queries.query1151_certified,N12Compact.HistoricalOwnership.Queries.query1152_certified,N12Compact.C979SharedSelections.selected1359,N12Compact.C979SharedSelections.selected1360,N12Compact.C979SharedSelections.selected1361,N12Compact.HistoricalOwnership.Queries.query1153_certified,N12Compact.C979SharedSelections.selected1362,N12Compact.HistoricalOwnership.Queries.query1154_certified,N12Compact.HistoricalOwnership.Queries.query1155_certified,N12Compact.C979SharedSelections.selected1363,N12Compact.HistoricalOwnership.Queries.query1156_certified,N12Compact.HistoricalOwnership.Queries.query1157_certified,N12Compact.HistoricalOwnership.Queries.query1158_certified,N12Compact.C979SharedSelections.selected1364,N12Compact.HistoricalOwnership.Queries.query1159_certified,N12Compact.HistoricalOwnership.Queries.query1160_certified,N12Compact.HistoricalOwnership.Queries.query1161_certified,N12Compact.HistoricalOwnership.Queries.query1162_certified,N12Compact.C979SharedSelections.selected1365,N12Compact.C979SharedSelections.selected1366,N12Compact.HistoricalOwnership.Queries.query1163_certified,N12Compact.C979SharedSelections.selected1367,N12Compact.HistoricalOwnership.Queries.query1164_certified,N12Compact.HistoricalOwnership.Queries.query1165_certified,N12Compact.C979SharedSelections.selected1368,N12Compact.HistoricalOwnership.Queries.query1166_certified,N12Compact.HistoricalOwnership.Queries.query1167_certified,N12Compact.HistoricalOwnership.Queries.query1168_certified,N12Compact.C979SharedSelections.selected1369,N12Compact.HistoricalOwnership.Queries.query1169_certified,N12Compact.HistoricalOwnership.Queries.query1170_certified,N12Compact.HistoricalOwnership.Queries.query1171_certified,N12Compact.HistoricalOwnership.Queries.query1172_certified,N12Compact.C979SharedSelections.selected1370,N12Compact.HistoricalOwnership.Queries.query1173_certified,N12Compact.HistoricalOwnership.Queries.query1174_certified,N12Compact.HistoricalOwnership.Queries.query1175_certified,N12Compact.HistoricalOwnership.Queries.query1176_certified,N12Compact.HistoricalOwnership.Queries.query1177_certified,N12Compact.C979SharedSelections.selected1371,N12Compact.C979SharedSelections.selected1372,N12Compact.C979SharedSelections.selected1373,N12Compact.HistoricalOwnership.Queries.query1178_certified,N12Compact.C979SharedSelections.selected1374,N12Compact.HistoricalOwnership.Queries.query1179_certified,N12Compact.HistoricalOwnership.Queries.query1180_certified,N12Compact.C979SharedSelections.selected1375,N12Compact.HistoricalOwnership.Queries.query1181_certified,N12Compact.HistoricalOwnership.Queries.query1182_certified,N12Compact.HistoricalOwnership.Queries.query1183_certified,N12Compact.C979SharedSelections.selected1376,N12Compact.HistoricalOwnership.Queries.query1184_certified,N12Compact.HistoricalOwnership.Queries.query1185_certified,N12Compact.HistoricalOwnership.Queries.query1186_certified,N12Compact.HistoricalOwnership.Queries.query1187_certified,N12Compact.C979SharedSelections.selected1377,N12Compact.HistoricalOwnership.Queries.query1188_certified,N12Compact.HistoricalOwnership.Queries.query1189_certified,N12Compact.HistoricalOwnership.Queries.query1190_certified,N12Compact.HistoricalOwnership.Queries.query1191_certified,N12Compact.HistoricalOwnership.Queries.query1192_certified,N12Compact.C979SharedSelections.selected1378,N12Compact.HistoricalOwnership.Queries.query1193_certified,N12Compact.HistoricalOwnership.Queries.query1194_certified,N12Compact.HistoricalOwnership.Queries.query1195_certified,N12Compact.HistoricalOwnership.Queries.query1196_certified,N12Compact.HistoricalOwnership.Queries.query1197_certified,N12Compact.HistoricalOwnership.Queries.query1198_certified,N12Compact.C979SharedSelections.selected1379,N12Compact.C979SharedSelections.selected1380,N12Compact.HistoricalOwnership.Queries.query1199_certified,N12Compact.C979SharedSelections.selected1381,N12Compact.HistoricalOwnership.Queries.query1200_certified,N12Compact.HistoricalOwnership.Queries.query1201_certified,N12Compact.C979SharedSelections.selected1382,N12Compact.HistoricalOwnership.Queries.query1202_certified,N12Compact.HistoricalOwnership.Queries.query1203_certified,N12Compact.HistoricalOwnership.Queries.query1204_certified,N12Compact.C979SharedSelections.selected1383,N12Compact.HistoricalOwnership.Queries.query1205_certified,N12Compact.HistoricalOwnership.Queries.query1206_certified,N12Compact.HistoricalOwnership.Queries.query1207_certified,N12Compact.HistoricalOwnership.Queries.query1208_certified,N12Compact.C979SharedSelections.selected1384,N12Compact.HistoricalOwnership.Queries.query1209_certified,N12Compact.HistoricalOwnership.Queries.query1210_certified,N12Compact.HistoricalOwnership.Queries.query1211_certified,N12Compact.HistoricalOwnership.Queries.query1212_certified,N12Compact.HistoricalOwnership.Queries.query1213_certified,N12Compact.HistoricalOwnership.Queries.query1214_certified,N12Compact.HistoricalOwnership.Queries.query1215_certified,N12Compact.HistoricalOwnership.Queries.query1216_certified,N12Compact.HistoricalOwnership.Queries.query1217_certified,N12Compact.HistoricalOwnership.Queries.query1218_certified,N12Compact.HistoricalOwnership.Queries.query1219_certified,N12Compact.C979SharedSelections.selected1385,N12Compact.HistoricalOwnership.Queries.query1220_certified,N12Compact.HistoricalOwnership.Queries.query1221_certified,N12Compact.HistoricalOwnership.Queries.query1222_certified,N12Compact.HistoricalOwnership.Queries.query1223_certified,N12Compact.HistoricalOwnership.Queries.query1224_certified,N12Compact.HistoricalOwnership.Queries.query1225_certified,N12Compact.HistoricalOwnership.Queries.query1226_certified,N12Compact.C979SharedSelections.selected1386,N12Compact.C979SharedSelections.selected1387,N12Compact.HistoricalOwnership.Queries.query1227_certified,N12Compact.C979SharedSelections.selected1388,N12Compact.HistoricalOwnership.Queries.query1228_certified,N12Compact.HistoricalOwnership.Queries.query1229_certified,N12Compact.C979SharedSelections.selected1389,N12Compact.HistoricalOwnership.Queries.query1230_certified,N12Compact.HistoricalOwnership.Queries.query1231_certified,N12Compact.HistoricalOwnership.Queries.query1232_certified,N12Compact.C979SharedSelections.selected1390,N12Compact.HistoricalOwnership.Queries.query1233_certified,N12Compact.HistoricalOwnership.Queries.query1234_certified,N12Compact.HistoricalOwnership.Queries.query1235_certified,N12Compact.HistoricalOwnership.Queries.query1236_certified,N12Compact.C979SharedSelections.selected1391,N12Compact.HistoricalOwnership.Queries.query1237_certified,N12Compact.HistoricalOwnership.Queries.query1238_certified,N12Compact.HistoricalOwnership.Queries.query1239_certified,N12Compact.HistoricalOwnership.Queries.query1240_certified,N12Compact.HistoricalOwnership.Queries.query1241_certified,N12Compact.HistoricalOwnership.Queries.query1242_certified,N12Compact.HistoricalOwnership.Queries.query1243_certified,N12Compact.HistoricalOwnership.Queries.query1244_certified,N12Compact.HistoricalOwnership.Queries.query1245_certified,N12Compact.HistoricalOwnership.Queries.query1246_certified,N12Compact.HistoricalOwnership.Queries.query1247_certified,N12Compact.C979SharedSelections.selected1392,N12Compact.HistoricalOwnership.Queries.query1248_certified,N12Compact.HistoricalOwnership.Queries.query1249_certified,N12Compact.HistoricalOwnership.Queries.query1250_certified,N12Compact.HistoricalOwnership.Queries.query1251_certified,N12Compact.HistoricalOwnership.Queries.query1252_certified,N12Compact.HistoricalOwnership.Queries.query1253_certified,N12Compact.HistoricalOwnership.Queries.query1254_certified,N12Compact.HistoricalOwnership.Queries.query1255_certified,N12Compact.HistoricalOwnership.Queries.query1256_certified,N12Compact.HistoricalOwnership.Queries.query1257_certified,N12Compact.HistoricalOwnership.Queries.query1258_certified,N12Compact.HistoricalOwnership.Queries.query1259_certified,N12Compact.HistoricalOwnership.Queries.query1260_certified,N12Compact.HistoricalOwnership.Queries.query1261_certified]⟩
private def single979_10_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16384,1,{0}),(16384,1,{1}),(16384,1,{0,1}),(16384,1,{2}),(16384,1,{0,2}),(16384,1,{1,2}),(16384,1,{0,1,2}),(16384,1,{3}),(16384,1,{0,3}),(16384,1,{1,3}),(16384,1,{0,1,3}),(16384,1,{2,3}),(16384,1,{0,2,3}),(16384,1,{1,2,3}),(16384,1,{4}),(16384,1,{0,4}),(16384,1,{1,4}),(16384,1,{0,1,4}),(16384,1,{2,4}),(16384,1,{0,2,4}),(16384,1,{1,2,4}),(16384,1,{3,4}),(16384,1,{0,3,4}),(16384,1,{1,3,4}),(16384,1,{2,3,4}),(16384,1,{5}),(16384,1,{0,5}),(16384,1,{1,5}),(16384,1,{0,1,5}),(16384,1,{2,5}),(16384,1,{0,2,5}),(16384,1,{1,2,5}),(16384,1,{3,5}),(16384,1,{0,3,5}),(16384,1,{1,3,5}),(16384,1,{2,3,5}),(16384,1,{4,5}),(16384,1,{0,4,5}),(16384,1,{1,4,5}),(16384,1,{2,4,5}),(16384,1,{3,4,5}),(16384,1,{0,6}),(16384,1,{1,6}),(16384,1,{0,1,6}),(16384,1,{2,6}),(16384,1,{0,2,6}),(16384,1,{1,2,6}),(16384,1,{3,6}),(16384,1,{0,3,6}),(16384,1,{1,3,6}),(16384,1,{2,3,6}),(16384,1,{4,6}),(16384,1,{0,4,6}),(16384,1,{1,4,6}),(16384,1,{2,4,6}),(16384,1,{3,4,6}),(16384,1,{5,6}),(16384,1,{0,5,6}),(16384,1,{1,5,6}),(16384,1,{2,5,6}),(16384,1,{3,5,6}),(16384,1,{4,5,6}),(16384,1,{7}),(16384,1,{0,7}),(16384,1,{1,7}),(16384,1,{0,1,7}),(16384,1,{2,7}),(16384,1,{0,2,7}),(16384,1,{1,2,7}),(16384,1,{3,7}),(16384,1,{0,3,7}),(16384,1,{1,3,7}),(16384,1,{2,3,7}),(16384,1,{4,7}),(16384,1,{0,4,7}),(16384,1,{1,4,7}),(16384,1,{2,4,7}),(16384,1,{3,4,7}),(16384,1,{5,7}),(16384,1,{0,5,7}),(16384,1,{1,5,7}),(16384,1,{2,5,7}),(16384,1,{3,5,7}),(16384,1,{4,5,7}),(16384,1,{6,7}),(16384,1,{0,6,7}),(16384,1,{1,6,7}),(16384,1,{2,6,7}),(16384,1,{3,6,7}),(16384,1,{4,6,7}),(16384,1,{5,6,7}),(16384,1,{0,8}),(16384,1,{1,8}),(16384,1,{0,1,8}),(16384,1,{2,8}),(16384,1,{0,2,8}),(16384,1,{1,2,8}),(16384,1,{3,8}),(16384,1,{0,3,8}),(16384,1,{1,3,8}),(16384,1,{2,3,8}),(16384,1,{4,8}),(16384,1,{0,4,8}),(16384,1,{1,4,8}),(16384,1,{2,4,8}),(16384,1,{3,4,8}),(16384,1,{5,8}),(16384,1,{0,5,8}),(16384,1,{1,5,8}),(16384,1,{2,5,8}),(16384,1,{3,5,8}),(16384,1,{4,5,8}),(16384,1,{0,6,8}),(16384,1,{1,6,8}),(16384,1,{2,6,8}),(16384,1,{3,6,8}),(16384,1,{4,6,8}),(16384,1,{5,6,8}),(16384,1,{7,8}),(16384,1,{0,7,8}),(16384,1,{1,7,8}),(16384,1,{2,7,8}),(16384,1,{3,7,8}),(16384,1,{4,7,8}),(16384,1,{5,7,8}),(16384,1,{6,7,8}),(16384,1,{0,9}),(16384,1,{1,9}),(16384,1,{0,1,9}),(16384,1,{2,9}),(16384,1,{0,2,9}),(16384,1,{1,2,9}),(16384,1,{3,9}),(16384,1,{0,3,9}),(16384,1,{1,3,9}),(16384,1,{2,3,9}),(16384,1,{4,9}),(16384,1,{0,4,9}),(16384,1,{1,4,9}),(16384,1,{2,4,9}),(16384,1,{3,4,9}),(16384,1,{5,9}),(16384,1,{0,5,9}),(16384,1,{1,5,9}),(16384,1,{2,5,9}),(16384,1,{3,5,9}),(16384,1,{4,5,9}),(16384,1,{0,6,9}),(16384,1,{1,6,9}),(16384,1,{2,6,9}),(16384,1,{3,6,9}),(16384,1,{4,6,9}),(16384,1,{5,6,9}),(16384,1,{7,9}),(16384,1,{0,7,9}),(16384,1,{1,7,9}),(16384,1,{2,7,9}),(16384,1,{3,7,9}),(16384,1,{4,7,9}),(16384,1,{5,7,9}),(16384,1,{6,7,9}),(16384,1,{0,8,9}),(16384,1,{1,8,9}),(16384,1,{2,8,9}),(16384,1,{3,8,9}),(16384,1,{4,8,9}),(16384,1,{5,8,9}),(16384,1,{7,8,9})]
private theorem single979_10_1_queries_exact :
    single979_10_1Signatures = single979_10_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_10_1_queries_exact

private def single979_10_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{6},{8},{6,8},{9},{6,9},{8,9},{6,8,9}] : List (Finset Nat)) ∨ (16384,1,owned) ∈ single979_10_1Signatures

private instance : DecidablePred single979_10_1_owned_claim := fun index => by
  unfold single979_10_1_owned_claim
  infer_instance

private theorem single979_10_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_10_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_10_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_10_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_10_1 case979Family 1 single979_10_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨16384,1,3,[{6},{8},{6,8},{9},{6,9},{8,9},{6,8,9}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_10_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_10_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_10_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_10_1_owned_block0
      · exact single979_10_1_owned_block1
      · exact single979_10_1_owned_block2
      · exact single979_10_1_owned_block3
      · exact single979_10_1_owned_block4
      · exact single979_10_1_owned_block5
      · exact single979_10_1_owned_block6
      · exact single979_10_1_owned_block7
      · exact single979_10_1_owned_block8
      · exact single979_10_1_owned_block9
      · exact single979_10_1_owned_block10
      · exact single979_10_1_owned_block11
      · exact single979_10_1_owned_block12
      · exact single979_10_1_owned_block13
      · exact single979_10_1_owned_block14
      · exact single979_10_1_owned_block15
      · exact single979_10_1_owned_block16
      · exact single979_10_1_owned_block17
      · exact single979_10_1_owned_block18
      · exact single979_10_1_owned_block19
      · exact single979_10_1_owned_block20
      · exact single979_10_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_10_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_10_1_metadata

theorem single979_10_1_checked : single979_10_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_10_1 case979Family 1
    single979_10_1Signatures single979_10_1_queries_exact (by decide) single979_10_1_metadata

end
end S12

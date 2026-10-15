import Compact.Core.FiniteKernelDecision
import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_11_1 : DirectSingleDomain := ⟨32768,1,3,[{4},{1,4},{7},{4,7},{1,4,7},{7,9},{4,7,9}],[N12Compact.C979SharedSelections.selected1585,N12Compact.C979SharedSelections.selected1586,N12Compact.C979SharedSelections.selected1587,N12Compact.C979SharedSelections.selected1588,N12Compact.C979SharedSelections.selected1589,N12Compact.C979SharedSelections.selected1590,N12Compact.HistoricalOwnership.Queries.query1264_certified,N12Compact.C979SharedSelections.selected1591,N12Compact.C979SharedSelections.selected1592,N12Compact.C979SharedSelections.selected1593,N12Compact.HistoricalOwnership.Queries.query1265_certified,N12Compact.C979SharedSelections.selected1594,N12Compact.HistoricalOwnership.Queries.query1266_certified,N12Compact.HistoricalOwnership.Queries.query1267_certified,N12Compact.C979SharedSelections.selected1595,N12Compact.HistoricalOwnership.Queries.query1268_certified,N12Compact.C979SharedSelections.selected1596,N12Compact.HistoricalOwnership.Queries.query1269_certified,N12Compact.HistoricalOwnership.Queries.query1270_certified,N12Compact.C979SharedSelections.selected1597,N12Compact.HistoricalOwnership.Queries.query1271_certified,N12Compact.HistoricalOwnership.Queries.query1272_certified,N12Compact.HistoricalOwnership.Queries.query1273_certified,N12Compact.C979SharedSelections.selected1598,N12Compact.C979SharedSelections.selected1599,N12Compact.C979SharedSelections.selected1600,N12Compact.HistoricalOwnership.Queries.query1274_certified,N12Compact.C979SharedSelections.selected1601,N12Compact.HistoricalOwnership.Queries.query1275_certified,N12Compact.HistoricalOwnership.Queries.query1276_certified,N12Compact.C979SharedSelections.selected1602,N12Compact.HistoricalOwnership.Queries.query1277_certified,N12Compact.HistoricalOwnership.Queries.query1278_certified,N12Compact.HistoricalOwnership.Queries.query1279_certified,N12Compact.C979SharedSelections.selected1603,N12Compact.HistoricalOwnership.Queries.query1280_certified,N12Compact.HistoricalOwnership.Queries.query1281_certified,N12Compact.HistoricalOwnership.Queries.query1282_certified,N12Compact.HistoricalOwnership.Queries.query1283_certified,N12Compact.C979SharedSelections.selected1604,N12Compact.C979SharedSelections.selected1605,N12Compact.C979SharedSelections.selected1606,N12Compact.HistoricalOwnership.Queries.query1284_certified,N12Compact.C979SharedSelections.selected1607,N12Compact.HistoricalOwnership.Queries.query1285_certified,N12Compact.HistoricalOwnership.Queries.query1286_certified,N12Compact.C979SharedSelections.selected1608,N12Compact.HistoricalOwnership.Queries.query1287_certified,N12Compact.HistoricalOwnership.Queries.query1288_certified,N12Compact.HistoricalOwnership.Queries.query1289_certified,N12Compact.C979SharedSelections.selected1609,N12Compact.HistoricalOwnership.Queries.query1290_certified,N12Compact.HistoricalOwnership.Queries.query1291_certified,N12Compact.HistoricalOwnership.Queries.query1292_certified,N12Compact.HistoricalOwnership.Queries.query1293_certified,N12Compact.C979SharedSelections.selected1610,N12Compact.HistoricalOwnership.Queries.query1294_certified,N12Compact.HistoricalOwnership.Queries.query1295_certified,N12Compact.HistoricalOwnership.Queries.query1296_certified,N12Compact.HistoricalOwnership.Queries.query1297_certified,N12Compact.HistoricalOwnership.Queries.query1298_certified,N12Compact.C979SharedSelections.selected1611,N12Compact.C979SharedSelections.selected1612,N12Compact.HistoricalOwnership.Queries.query1299_certified,N12Compact.C979SharedSelections.selected1613,N12Compact.HistoricalOwnership.Queries.query1300_certified,N12Compact.HistoricalOwnership.Queries.query1301_certified,N12Compact.C979SharedSelections.selected1614,N12Compact.HistoricalOwnership.Queries.query1302_certified,N12Compact.HistoricalOwnership.Queries.query1303_certified,N12Compact.HistoricalOwnership.Queries.query1304_certified,N12Compact.HistoricalOwnership.Queries.query1305_certified,N12Compact.HistoricalOwnership.Queries.query1306_certified,N12Compact.HistoricalOwnership.Queries.query1307_certified,N12Compact.C979SharedSelections.selected1615,N12Compact.HistoricalOwnership.Queries.query1308_certified,N12Compact.HistoricalOwnership.Queries.query1309_certified,N12Compact.HistoricalOwnership.Queries.query1310_certified,N12Compact.HistoricalOwnership.Queries.query1311_certified,N12Compact.HistoricalOwnership.Queries.query1312_certified,N12Compact.C979SharedSelections.selected1616,N12Compact.HistoricalOwnership.Queries.query1313_certified,N12Compact.HistoricalOwnership.Queries.query1314_certified,N12Compact.HistoricalOwnership.Queries.query1315_certified,N12Compact.HistoricalOwnership.Queries.query1316_certified,N12Compact.HistoricalOwnership.Queries.query1317_certified,N12Compact.HistoricalOwnership.Queries.query1318_certified,N12Compact.C979SharedSelections.selected1617,N12Compact.C979SharedSelections.selected1618,N12Compact.C979SharedSelections.selected1619,N12Compact.HistoricalOwnership.Queries.query1319_certified,N12Compact.C979SharedSelections.selected1620,N12Compact.HistoricalOwnership.Queries.query1320_certified,N12Compact.HistoricalOwnership.Queries.query1321_certified,N12Compact.C979SharedSelections.selected1621,N12Compact.HistoricalOwnership.Queries.query1322_certified,N12Compact.HistoricalOwnership.Queries.query1323_certified,N12Compact.HistoricalOwnership.Queries.query1324_certified,N12Compact.C979SharedSelections.selected1622,N12Compact.HistoricalOwnership.Queries.query1325_certified,N12Compact.HistoricalOwnership.Queries.query1326_certified,N12Compact.HistoricalOwnership.Queries.query1327_certified,N12Compact.HistoricalOwnership.Queries.query1328_certified,N12Compact.C979SharedSelections.selected1623,N12Compact.HistoricalOwnership.Queries.query1329_certified,N12Compact.HistoricalOwnership.Queries.query1330_certified,N12Compact.HistoricalOwnership.Queries.query1331_certified,N12Compact.HistoricalOwnership.Queries.query1332_certified,N12Compact.HistoricalOwnership.Queries.query1333_certified,N12Compact.C979SharedSelections.selected1624,N12Compact.HistoricalOwnership.Queries.query1334_certified,N12Compact.HistoricalOwnership.Queries.query1335_certified,N12Compact.HistoricalOwnership.Queries.query1336_certified,N12Compact.HistoricalOwnership.Queries.query1337_certified,N12Compact.HistoricalOwnership.Queries.query1338_certified,N12Compact.HistoricalOwnership.Queries.query1339_certified,N12Compact.C979SharedSelections.selected1625,N12Compact.HistoricalOwnership.Queries.query1340_certified,N12Compact.HistoricalOwnership.Queries.query1341_certified,N12Compact.HistoricalOwnership.Queries.query1342_certified,N12Compact.HistoricalOwnership.Queries.query1343_certified,N12Compact.HistoricalOwnership.Queries.query1344_certified,N12Compact.HistoricalOwnership.Queries.query1345_certified,N12Compact.HistoricalOwnership.Queries.query1346_certified,N12Compact.C979SharedSelections.selected1626,N12Compact.C979SharedSelections.selected1627,N12Compact.C979SharedSelections.selected1628,N12Compact.HistoricalOwnership.Queries.query1347_certified,N12Compact.C979SharedSelections.selected1629,N12Compact.HistoricalOwnership.Queries.query1348_certified,N12Compact.HistoricalOwnership.Queries.query1349_certified,N12Compact.C979SharedSelections.selected1630,N12Compact.HistoricalOwnership.Queries.query1350_certified,N12Compact.HistoricalOwnership.Queries.query1351_certified,N12Compact.HistoricalOwnership.Queries.query1352_certified,N12Compact.C979SharedSelections.selected1631,N12Compact.HistoricalOwnership.Queries.query1353_certified,N12Compact.HistoricalOwnership.Queries.query1354_certified,N12Compact.HistoricalOwnership.Queries.query1355_certified,N12Compact.HistoricalOwnership.Queries.query1356_certified,N12Compact.C979SharedSelections.selected1632,N12Compact.HistoricalOwnership.Queries.query1357_certified,N12Compact.HistoricalOwnership.Queries.query1358_certified,N12Compact.HistoricalOwnership.Queries.query1359_certified,N12Compact.HistoricalOwnership.Queries.query1360_certified,N12Compact.HistoricalOwnership.Queries.query1361_certified,N12Compact.C979SharedSelections.selected1633,N12Compact.HistoricalOwnership.Queries.query1362_certified,N12Compact.HistoricalOwnership.Queries.query1363_certified,N12Compact.HistoricalOwnership.Queries.query1364_certified,N12Compact.HistoricalOwnership.Queries.query1365_certified,N12Compact.HistoricalOwnership.Queries.query1366_certified,N12Compact.HistoricalOwnership.Queries.query1367_certified,N12Compact.HistoricalOwnership.Queries.query1368_certified,N12Compact.HistoricalOwnership.Queries.query1369_certified,N12Compact.HistoricalOwnership.Queries.query1370_certified,N12Compact.HistoricalOwnership.Queries.query1371_certified,N12Compact.HistoricalOwnership.Queries.query1372_certified,N12Compact.HistoricalOwnership.Queries.query1373_certified,N12Compact.C979SharedSelections.selected1634,N12Compact.HistoricalOwnership.Queries.query1374_certified,N12Compact.HistoricalOwnership.Queries.query1375_certified,N12Compact.HistoricalOwnership.Queries.query1376_certified,N12Compact.HistoricalOwnership.Queries.query1377_certified,N12Compact.HistoricalOwnership.Queries.query1378_certified,N12Compact.HistoricalOwnership.Queries.query1379_certified,N12Compact.HistoricalOwnership.Queries.query1380_certified,N12Compact.HistoricalOwnership.Queries.query1381_certified]⟩
private def single979_11_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32768,1,{0}),(32768,1,{1}),(32768,1,{0,1}),(32768,1,{2}),(32768,1,{0,2}),(32768,1,{1,2}),(32768,1,{0,1,2}),(32768,1,{3}),(32768,1,{0,3}),(32768,1,{1,3}),(32768,1,{0,1,3}),(32768,1,{2,3}),(32768,1,{0,2,3}),(32768,1,{1,2,3}),(32768,1,{0,4}),(32768,1,{0,1,4}),(32768,1,{2,4}),(32768,1,{0,2,4}),(32768,1,{1,2,4}),(32768,1,{3,4}),(32768,1,{0,3,4}),(32768,1,{1,3,4}),(32768,1,{2,3,4}),(32768,1,{5}),(32768,1,{0,5}),(32768,1,{1,5}),(32768,1,{0,1,5}),(32768,1,{2,5}),(32768,1,{0,2,5}),(32768,1,{1,2,5}),(32768,1,{3,5}),(32768,1,{0,3,5}),(32768,1,{1,3,5}),(32768,1,{2,3,5}),(32768,1,{4,5}),(32768,1,{0,4,5}),(32768,1,{1,4,5}),(32768,1,{2,4,5}),(32768,1,{3,4,5}),(32768,1,{6}),(32768,1,{0,6}),(32768,1,{1,6}),(32768,1,{0,1,6}),(32768,1,{2,6}),(32768,1,{0,2,6}),(32768,1,{1,2,6}),(32768,1,{3,6}),(32768,1,{0,3,6}),(32768,1,{1,3,6}),(32768,1,{2,3,6}),(32768,1,{4,6}),(32768,1,{0,4,6}),(32768,1,{1,4,6}),(32768,1,{2,4,6}),(32768,1,{3,4,6}),(32768,1,{5,6}),(32768,1,{0,5,6}),(32768,1,{1,5,6}),(32768,1,{2,5,6}),(32768,1,{3,5,6}),(32768,1,{4,5,6}),(32768,1,{0,7}),(32768,1,{1,7}),(32768,1,{0,1,7}),(32768,1,{2,7}),(32768,1,{0,2,7}),(32768,1,{1,2,7}),(32768,1,{3,7}),(32768,1,{0,3,7}),(32768,1,{1,3,7}),(32768,1,{2,3,7}),(32768,1,{0,4,7}),(32768,1,{2,4,7}),(32768,1,{3,4,7}),(32768,1,{5,7}),(32768,1,{0,5,7}),(32768,1,{1,5,7}),(32768,1,{2,5,7}),(32768,1,{3,5,7}),(32768,1,{4,5,7}),(32768,1,{6,7}),(32768,1,{0,6,7}),(32768,1,{1,6,7}),(32768,1,{2,6,7}),(32768,1,{3,6,7}),(32768,1,{4,6,7}),(32768,1,{5,6,7}),(32768,1,{8}),(32768,1,{0,8}),(32768,1,{1,8}),(32768,1,{0,1,8}),(32768,1,{2,8}),(32768,1,{0,2,8}),(32768,1,{1,2,8}),(32768,1,{3,8}),(32768,1,{0,3,8}),(32768,1,{1,3,8}),(32768,1,{2,3,8}),(32768,1,{4,8}),(32768,1,{0,4,8}),(32768,1,{1,4,8}),(32768,1,{2,4,8}),(32768,1,{3,4,8}),(32768,1,{5,8}),(32768,1,{0,5,8}),(32768,1,{1,5,8}),(32768,1,{2,5,8}),(32768,1,{3,5,8}),(32768,1,{4,5,8}),(32768,1,{6,8}),(32768,1,{0,6,8}),(32768,1,{1,6,8}),(32768,1,{2,6,8}),(32768,1,{3,6,8}),(32768,1,{4,6,8}),(32768,1,{5,6,8}),(32768,1,{7,8}),(32768,1,{0,7,8}),(32768,1,{1,7,8}),(32768,1,{2,7,8}),(32768,1,{3,7,8}),(32768,1,{4,7,8}),(32768,1,{5,7,8}),(32768,1,{6,7,8}),(32768,1,{9}),(32768,1,{0,9}),(32768,1,{1,9}),(32768,1,{0,1,9}),(32768,1,{2,9}),(32768,1,{0,2,9}),(32768,1,{1,2,9}),(32768,1,{3,9}),(32768,1,{0,3,9}),(32768,1,{1,3,9}),(32768,1,{2,3,9}),(32768,1,{4,9}),(32768,1,{0,4,9}),(32768,1,{1,4,9}),(32768,1,{2,4,9}),(32768,1,{3,4,9}),(32768,1,{5,9}),(32768,1,{0,5,9}),(32768,1,{1,5,9}),(32768,1,{2,5,9}),(32768,1,{3,5,9}),(32768,1,{4,5,9}),(32768,1,{6,9}),(32768,1,{0,6,9}),(32768,1,{1,6,9}),(32768,1,{2,6,9}),(32768,1,{3,6,9}),(32768,1,{4,6,9}),(32768,1,{5,6,9}),(32768,1,{0,7,9}),(32768,1,{1,7,9}),(32768,1,{2,7,9}),(32768,1,{3,7,9}),(32768,1,{5,7,9}),(32768,1,{6,7,9}),(32768,1,{8,9}),(32768,1,{0,8,9}),(32768,1,{1,8,9}),(32768,1,{2,8,9}),(32768,1,{3,8,9}),(32768,1,{4,8,9}),(32768,1,{5,8,9}),(32768,1,{6,8,9}),(32768,1,{7,8,9})]
private theorem single979_11_1_queries_exact :
    single979_11_1Signatures = single979_11_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_11_1_queries_exact

private def single979_11_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{4},{1,4},{7},{4,7},{1,4,7},{7,9},{4,7,9}] : List (Finset Nat)) ∨ (32768,1,owned) ∈ single979_11_1Signatures

private instance : DecidablePred single979_11_1_owned_claim := fun index => by
  unfold single979_11_1_owned_claim
  infer_instance

private theorem single979_11_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single979_11_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single979_11_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single979_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single979_11_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single979_11_1 case979Family 1 single979_11_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨32768,1,3,[{4},{1,4},{7},{4,7},{1,4,7},{7,9},{4,7,9}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_11_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single979_11_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single979_11_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single979_11_1_owned_block0
      · exact single979_11_1_owned_block1
      · exact single979_11_1_owned_block2
      · exact single979_11_1_owned_block3
      · exact single979_11_1_owned_block4
      · exact single979_11_1_owned_block5
      · exact single979_11_1_owned_block6
      · exact single979_11_1_owned_block7
      · exact single979_11_1_owned_block8
      · exact single979_11_1_owned_block9
      · exact single979_11_1_owned_block10
      · exact single979_11_1_owned_block11
      · exact single979_11_1_owned_block12
      · exact single979_11_1_owned_block13
      · exact single979_11_1_owned_block14
      · exact single979_11_1_owned_block15
      · exact single979_11_1_owned_block16
      · exact single979_11_1_owned_block17
      · exact single979_11_1_owned_block18
      · exact single979_11_1_owned_block19
      · exact single979_11_1_owned_block20
      · exact single979_11_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single979_11_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high
#check single979_11_1_metadata

theorem single979_11_1_checked : single979_11_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single979_11_1 case979Family 1
    single979_11_1Signatures single979_11_1_queries_exact (by decide) single979_11_1_metadata


end
end S12

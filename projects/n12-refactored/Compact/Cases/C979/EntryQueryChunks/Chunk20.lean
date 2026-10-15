import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_10_0 : DirectSingleDomain := ⟨16384,1,2,[{8},{6,8},{9},{7,9},{8,9}],[N12Compact.C979SharedSelections.selected1294,N12Compact.C979SharedSelections.selected1295,N12Compact.C979SharedSelections.selected1296,N12Compact.C979SharedSelections.selected1297,N12Compact.C979SharedSelections.selected1298,N12Compact.C979SharedSelections.selected1299,N12Compact.C979SharedSelections.selected1300,N12Compact.C979SharedSelections.selected1301,N12Compact.C979SharedSelections.selected1302,N12Compact.C979SharedSelections.selected1303,N12Compact.C979SharedSelections.selected1304,N12Compact.C979SharedSelections.selected1305,N12Compact.C979SharedSelections.selected1306,N12Compact.C979SharedSelections.selected1307,N12Compact.C979SharedSelections.selected1308,N12Compact.C979SharedSelections.selected1309,N12Compact.C979SharedSelections.selected1310,N12Compact.C979SharedSelections.selected1311,N12Compact.C979SharedSelections.selected1312,N12Compact.C979SharedSelections.selected1313,N12Compact.C979SharedSelections.selected1314,N12Compact.C979SharedSelections.selected1315,N12Compact.C979SharedSelections.selected1316,N12Compact.C979SharedSelections.selected1317,N12Compact.C979SharedSelections.selected1318,N12Compact.C979SharedSelections.selected1319,N12Compact.C979SharedSelections.selected1320,N12Compact.C979SharedSelections.selected1321,N12Compact.C979SharedSelections.selected1322,N12Compact.C979SharedSelections.selected1323,N12Compact.C979SharedSelections.selected1324,N12Compact.C979SharedSelections.selected1325,N12Compact.C979SharedSelections.selected1326,N12Compact.C979SharedSelections.selected1327,N12Compact.C979SharedSelections.selected1328,N12Compact.C979SharedSelections.selected1329,N12Compact.C979SharedSelections.selected1330,N12Compact.C979SharedSelections.selected1331,N12Compact.C979SharedSelections.selected1332,N12Compact.C979SharedSelections.selected1333,N12Compact.C979SharedSelections.selected1334,N12Compact.C979SharedSelections.selected1335,N12Compact.C979SharedSelections.selected1336,N12Compact.C979SharedSelections.selected1337,N12Compact.C979SharedSelections.selected1338,N12Compact.C979SharedSelections.selected1339,N12Compact.C979SharedSelections.selected1340,N12Compact.C979SharedSelections.selected1341,N12Compact.C979SharedSelections.selected1342,N12Compact.C979SharedSelections.selected1343]⟩
private def single979_10_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16384,0,{0}),(16384,0,{1}),(16384,0,{0,1}),(16384,0,{2}),(16384,0,{0,2}),(16384,0,{1,2}),(16384,0,{3}),(16384,0,{0,3}),(16384,0,{1,3}),(16384,0,{2,3}),(16384,0,{4}),(16384,0,{0,4}),(16384,0,{1,4}),(16384,0,{2,4}),(16384,0,{3,4}),(16384,0,{5}),(16384,0,{0,5}),(16384,0,{1,5}),(16384,0,{2,5}),(16384,0,{3,5}),(16384,0,{4,5}),(16384,0,{6}),(16384,0,{0,6}),(16384,0,{1,6}),(16384,0,{2,6}),(16384,0,{3,6}),(16384,0,{4,6}),(16384,0,{5,6}),(16384,0,{7}),(16384,0,{0,7}),(16384,0,{1,7}),(16384,0,{2,7}),(16384,0,{3,7}),(16384,0,{4,7}),(16384,0,{5,7}),(16384,0,{6,7}),(16384,0,{0,8}),(16384,0,{1,8}),(16384,0,{2,8}),(16384,0,{3,8}),(16384,0,{4,8}),(16384,0,{5,8}),(16384,0,{7,8}),(16384,0,{0,9}),(16384,0,{1,9}),(16384,0,{2,9}),(16384,0,{3,9}),(16384,0,{4,9}),(16384,0,{5,9}),(16384,0,{6,9})]
private theorem single979_10_0_queries_exact :
    single979_10_0Signatures = single979_10_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_10_0_queries_exact

private theorem single979_10_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_10_0 case979Family 0 single979_10_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨16384,1,2,[{8},{6,8},{9},{7,9},{8,9}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_10_0Signatures
  decide +kernel
#check single979_10_0_metadata

theorem single979_10_0_checked : single979_10_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_10_0 case979Family 0
    single979_10_0Signatures single979_10_0_queries_exact (by decide) single979_10_0_metadata

end
end S12

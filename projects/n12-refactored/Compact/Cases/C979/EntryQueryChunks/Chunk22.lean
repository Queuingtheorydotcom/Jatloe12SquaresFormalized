import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_11_0 : DirectSingleDomain := ⟨32768,1,2,[{3},{5},{3,5},{7},{3,7},{5,7}],[N12Compact.C979SharedSelections.selected1536,N12Compact.C979SharedSelections.selected1537,N12Compact.C979SharedSelections.selected1538,N12Compact.C979SharedSelections.selected1539,N12Compact.C979SharedSelections.selected1540,N12Compact.C979SharedSelections.selected1541,N12Compact.C979SharedSelections.selected1542,N12Compact.C979SharedSelections.selected1543,N12Compact.C979SharedSelections.selected1544,N12Compact.C979SharedSelections.selected1545,N12Compact.C979SharedSelections.selected1546,N12Compact.C979SharedSelections.selected1547,N12Compact.C979SharedSelections.selected1548,N12Compact.C979SharedSelections.selected1549,N12Compact.C979SharedSelections.selected1550,N12Compact.C979SharedSelections.selected1551,N12Compact.C979SharedSelections.selected1552,N12Compact.C979SharedSelections.selected1553,N12Compact.C979SharedSelections.selected1554,N12Compact.C979SharedSelections.selected1555,N12Compact.C979SharedSelections.selected1556,N12Compact.C979SharedSelections.selected1557,N12Compact.C979SharedSelections.selected1558,N12Compact.C979SharedSelections.selected1559,N12Compact.C979SharedSelections.selected1560,N12Compact.C979SharedSelections.selected1561,N12Compact.C979SharedSelections.selected1562,N12Compact.C979SharedSelections.selected1563,N12Compact.C979SharedSelections.selected1564,N12Compact.C979SharedSelections.selected1565,N12Compact.C979SharedSelections.selected1566,N12Compact.C979SharedSelections.selected1567,N12Compact.C979SharedSelections.selected1568,N12Compact.C979SharedSelections.selected1569,N12Compact.C979SharedSelections.selected1570,N12Compact.C979SharedSelections.selected1571,N12Compact.C979SharedSelections.selected1572,N12Compact.C979SharedSelections.selected1573,N12Compact.C979SharedSelections.selected1574,N12Compact.C979SharedSelections.selected1575,N12Compact.C979SharedSelections.selected1576,N12Compact.C979SharedSelections.selected1577,N12Compact.C979SharedSelections.selected1578,N12Compact.C979SharedSelections.selected1579,N12Compact.C979SharedSelections.selected1580,N12Compact.C979SharedSelections.selected1581,N12Compact.C979SharedSelections.selected1582,N12Compact.C979SharedSelections.selected1583,N12Compact.C979SharedSelections.selected1584]⟩
private def single979_11_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32768,0,{0}),(32768,0,{1}),(32768,0,{0,1}),(32768,0,{2}),(32768,0,{0,2}),(32768,0,{1,2}),(32768,0,{0,3}),(32768,0,{1,3}),(32768,0,{2,3}),(32768,0,{4}),(32768,0,{0,4}),(32768,0,{1,4}),(32768,0,{2,4}),(32768,0,{3,4}),(32768,0,{0,5}),(32768,0,{1,5}),(32768,0,{2,5}),(32768,0,{4,5}),(32768,0,{6}),(32768,0,{0,6}),(32768,0,{1,6}),(32768,0,{2,6}),(32768,0,{3,6}),(32768,0,{4,6}),(32768,0,{5,6}),(32768,0,{0,7}),(32768,0,{1,7}),(32768,0,{2,7}),(32768,0,{4,7}),(32768,0,{6,7}),(32768,0,{8}),(32768,0,{0,8}),(32768,0,{1,8}),(32768,0,{2,8}),(32768,0,{3,8}),(32768,0,{4,8}),(32768,0,{5,8}),(32768,0,{6,8}),(32768,0,{7,8}),(32768,0,{9}),(32768,0,{0,9}),(32768,0,{1,9}),(32768,0,{2,9}),(32768,0,{3,9}),(32768,0,{4,9}),(32768,0,{5,9}),(32768,0,{6,9}),(32768,0,{7,9}),(32768,0,{8,9})]
private theorem single979_11_0_queries_exact :
    single979_11_0Signatures = single979_11_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_11_0_queries_exact

private theorem single979_11_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_11_0 case979Family 0 single979_11_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨32768,1,2,[{3},{5},{3,5},{7},{3,7},{5,7}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_11_0Signatures
  decide +kernel
#check single979_11_0_metadata

theorem single979_11_0_checked : single979_11_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_11_0 case979Family 0
    single979_11_0Signatures single979_11_0_queries_exact (by decide) single979_11_0_metadata

end
end S12

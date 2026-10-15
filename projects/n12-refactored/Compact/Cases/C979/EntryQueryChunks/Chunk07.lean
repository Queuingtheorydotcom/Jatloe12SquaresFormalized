import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_3_1 : DirectSingleDomain := ⟨48,0,2,[∅,{7},{9},{7,9}],[N12Compact.HistoricalOwnership.Queries.query1395_certified,N12Compact.HistoricalOwnership.Queries.query1396_certified,N12Compact.HistoricalOwnership.Queries.query1683_certified,N12Compact.HistoricalOwnership.Queries.query1397_certified,N12Compact.HistoricalOwnership.Queries.query1684_certified,N12Compact.HistoricalOwnership.Queries.query1685_certified,N12Compact.HistoricalOwnership.Queries.query1398_certified,N12Compact.HistoricalOwnership.Queries.query1686_certified,N12Compact.HistoricalOwnership.Queries.query1687_certified,N12Compact.HistoricalOwnership.Queries.query1688_certified,N12Compact.HistoricalOwnership.Queries.query1399_certified,N12Compact.HistoricalOwnership.Queries.query1689_certified,N12Compact.HistoricalOwnership.Queries.query1690_certified,N12Compact.HistoricalOwnership.Queries.query1691_certified,N12Compact.HistoricalOwnership.Queries.query1692_certified,N12Compact.HistoricalOwnership.Queries.query1400_certified,N12Compact.HistoricalOwnership.Queries.query1693_certified,N12Compact.HistoricalOwnership.Queries.query1694_certified,N12Compact.HistoricalOwnership.Queries.query1695_certified,N12Compact.HistoricalOwnership.Queries.query1696_certified,N12Compact.HistoricalOwnership.Queries.query1697_certified,N12Compact.HistoricalOwnership.Queries.query1401_certified,N12Compact.HistoricalOwnership.Queries.query1698_certified,N12Compact.HistoricalOwnership.Queries.query1699_certified,N12Compact.HistoricalOwnership.Queries.query1700_certified,N12Compact.HistoricalOwnership.Queries.query1701_certified,N12Compact.HistoricalOwnership.Queries.query1702_certified,N12Compact.HistoricalOwnership.Queries.query1703_certified,N12Compact.HistoricalOwnership.Queries.query1704_certified,N12Compact.HistoricalOwnership.Queries.query1705_certified,N12Compact.HistoricalOwnership.Queries.query1706_certified,N12Compact.HistoricalOwnership.Queries.query1707_certified,N12Compact.HistoricalOwnership.Queries.query1708_certified,N12Compact.HistoricalOwnership.Queries.query1709_certified,N12Compact.HistoricalOwnership.Queries.query1710_certified,N12Compact.HistoricalOwnership.Queries.query1402_certified,N12Compact.HistoricalOwnership.Queries.query1711_certified,N12Compact.HistoricalOwnership.Queries.query1712_certified,N12Compact.HistoricalOwnership.Queries.query1713_certified,N12Compact.HistoricalOwnership.Queries.query1714_certified,N12Compact.HistoricalOwnership.Queries.query1715_certified,N12Compact.HistoricalOwnership.Queries.query1716_certified,N12Compact.HistoricalOwnership.Queries.query1717_certified,N12Compact.HistoricalOwnership.Queries.query1718_certified,N12Compact.HistoricalOwnership.Queries.query1719_certified,N12Compact.HistoricalOwnership.Queries.query1720_certified,N12Compact.HistoricalOwnership.Queries.query1721_certified,N12Compact.HistoricalOwnership.Queries.query1722_certified,N12Compact.HistoricalOwnership.Queries.query1723_certified,N12Compact.HistoricalOwnership.Queries.query1724_certified,N12Compact.HistoricalOwnership.Queries.query1725_certified,N12Compact.HistoricalOwnership.Queries.query1726_certified]⟩
private def single979_3_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(48,1,{0}),(48,1,{1}),(48,1,{0,1}),(48,1,{2}),(48,1,{0,2}),(48,1,{1,2}),(48,1,{3}),(48,1,{0,3}),(48,1,{1,3}),(48,1,{2,3}),(48,1,{4}),(48,1,{0,4}),(48,1,{1,4}),(48,1,{2,4}),(48,1,{3,4}),(48,1,{5}),(48,1,{0,5}),(48,1,{1,5}),(48,1,{2,5}),(48,1,{3,5}),(48,1,{4,5}),(48,1,{6}),(48,1,{0,6}),(48,1,{1,6}),(48,1,{2,6}),(48,1,{3,6}),(48,1,{4,6}),(48,1,{5,6}),(48,1,{0,7}),(48,1,{1,7}),(48,1,{2,7}),(48,1,{3,7}),(48,1,{4,7}),(48,1,{5,7}),(48,1,{6,7}),(48,1,{8}),(48,1,{0,8}),(48,1,{1,8}),(48,1,{2,8}),(48,1,{3,8}),(48,1,{4,8}),(48,1,{5,8}),(48,1,{6,8}),(48,1,{7,8}),(48,1,{0,9}),(48,1,{1,9}),(48,1,{2,9}),(48,1,{3,9}),(48,1,{4,9}),(48,1,{5,9}),(48,1,{6,9}),(48,1,{8,9})]
private theorem single979_3_1_queries_exact :
    single979_3_1Signatures = single979_3_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_3_1_queries_exact

private theorem single979_3_1_metadata :
    N12Compact.SmallOwnerDomain.Check single979_3_1 case979Family 1 single979_3_1Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨48,0,2,[∅,{7},{9},{7,9}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_3_1Signatures
  decide +kernel
#check single979_3_1_metadata

theorem single979_3_1_checked : single979_3_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomain.checked single979_3_1 case979Family 1
    single979_3_1Signatures single979_3_1_queries_exact (by decide) single979_3_1_metadata

end
end S12

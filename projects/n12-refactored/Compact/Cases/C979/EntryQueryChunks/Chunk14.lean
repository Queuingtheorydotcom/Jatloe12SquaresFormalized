import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_7_0 : DirectSingleDomain := ⟨3072,1,2,[{5},{0,5},{1,5},{3,5},{4,5},{5,7},{5,8},{5,9}],[N12Compact.HistoricalOwnership.Queries.query857_certified,N12Compact.HistoricalOwnership.Queries.query858_certified,N12Compact.HistoricalOwnership.Queries.query2090_certified,N12Compact.HistoricalOwnership.Queries.query859_certified,N12Compact.HistoricalOwnership.Queries.query2091_certified,N12Compact.HistoricalOwnership.Queries.query2092_certified,N12Compact.HistoricalOwnership.Queries.query860_certified,N12Compact.HistoricalOwnership.Queries.query2093_certified,N12Compact.HistoricalOwnership.Queries.query2094_certified,N12Compact.HistoricalOwnership.Queries.query2095_certified,N12Compact.HistoricalOwnership.Queries.query861_certified,N12Compact.HistoricalOwnership.Queries.query2096_certified,N12Compact.HistoricalOwnership.Queries.query2097_certified,N12Compact.HistoricalOwnership.Queries.query2098_certified,N12Compact.HistoricalOwnership.Queries.query2099_certified,N12Compact.HistoricalOwnership.Queries.query2100_certified,N12Compact.HistoricalOwnership.Queries.query862_certified,N12Compact.HistoricalOwnership.Queries.query2101_certified,N12Compact.HistoricalOwnership.Queries.query2102_certified,N12Compact.HistoricalOwnership.Queries.query2103_certified,N12Compact.HistoricalOwnership.Queries.query2104_certified,N12Compact.HistoricalOwnership.Queries.query2105_certified,N12Compact.HistoricalOwnership.Queries.query2106_certified,N12Compact.HistoricalOwnership.Queries.query863_certified,N12Compact.HistoricalOwnership.Queries.query2107_certified,N12Compact.HistoricalOwnership.Queries.query2108_certified,N12Compact.HistoricalOwnership.Queries.query2109_certified,N12Compact.HistoricalOwnership.Queries.query2110_certified,N12Compact.HistoricalOwnership.Queries.query2111_certified,N12Compact.HistoricalOwnership.Queries.query2112_certified,N12Compact.HistoricalOwnership.Queries.query864_certified,N12Compact.HistoricalOwnership.Queries.query2113_certified,N12Compact.HistoricalOwnership.Queries.query2114_certified,N12Compact.HistoricalOwnership.Queries.query2115_certified,N12Compact.HistoricalOwnership.Queries.query2116_certified,N12Compact.HistoricalOwnership.Queries.query2117_certified,N12Compact.HistoricalOwnership.Queries.query2118_certified,N12Compact.HistoricalOwnership.Queries.query2119_certified,N12Compact.HistoricalOwnership.Queries.query865_certified,N12Compact.HistoricalOwnership.Queries.query2120_certified,N12Compact.HistoricalOwnership.Queries.query2121_certified,N12Compact.HistoricalOwnership.Queries.query2122_certified,N12Compact.HistoricalOwnership.Queries.query2123_certified,N12Compact.HistoricalOwnership.Queries.query2124_certified,N12Compact.HistoricalOwnership.Queries.query2125_certified,N12Compact.HistoricalOwnership.Queries.query2126_certified,N12Compact.HistoricalOwnership.Queries.query2127_certified]⟩
private def single979_7_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(3072,0,{0}),(3072,0,{1}),(3072,0,{0,1}),(3072,0,{2}),(3072,0,{0,2}),(3072,0,{1,2}),(3072,0,{3}),(3072,0,{0,3}),(3072,0,{1,3}),(3072,0,{2,3}),(3072,0,{4}),(3072,0,{0,4}),(3072,0,{1,4}),(3072,0,{2,4}),(3072,0,{3,4}),(3072,0,{2,5}),(3072,0,{6}),(3072,0,{0,6}),(3072,0,{1,6}),(3072,0,{2,6}),(3072,0,{3,6}),(3072,0,{4,6}),(3072,0,{5,6}),(3072,0,{7}),(3072,0,{0,7}),(3072,0,{1,7}),(3072,0,{2,7}),(3072,0,{3,7}),(3072,0,{4,7}),(3072,0,{6,7}),(3072,0,{8}),(3072,0,{0,8}),(3072,0,{1,8}),(3072,0,{2,8}),(3072,0,{3,8}),(3072,0,{4,8}),(3072,0,{6,8}),(3072,0,{7,8}),(3072,0,{9}),(3072,0,{0,9}),(3072,0,{1,9}),(3072,0,{2,9}),(3072,0,{3,9}),(3072,0,{4,9}),(3072,0,{6,9}),(3072,0,{7,9}),(3072,0,{8,9})]
private theorem single979_7_0_queries_exact :
    single979_7_0Signatures = single979_7_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_7_0_queries_exact

private theorem single979_7_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_7_0 case979Family 0 single979_7_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨3072,1,2,[{5},{0,5},{1,5},{3,5},{4,5},{5,7},{5,8},{5,9}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_7_0Signatures
  decide +kernel
#check single979_7_0_metadata

theorem single979_7_0_checked : single979_7_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_7_0 case979Family 0
    single979_7_0Signatures single979_7_0_queries_exact (by decide) single979_7_0_metadata

end
end S12

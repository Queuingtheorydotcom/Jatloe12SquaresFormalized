import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_7_1 : DirectSingleDomain := ⟨3072,0,2,[∅,{1},{3},{1,3},{4},{1,4},{3,4},{6},{1,6},{3,6},{4,6},{7},{1,7},{3,7},{4,7},{6,7},{9},{1,9},{3,9},{4,9},{6,9},{7,9}],[N12Compact.HistoricalOwnership.Queries.query866_certified,N12Compact.HistoricalOwnership.Queries.query867_certified,N12Compact.HistoricalOwnership.Queries.query868_certified,N12Compact.HistoricalOwnership.Queries.query869_certified,N12Compact.HistoricalOwnership.Queries.query870_certified,N12Compact.HistoricalOwnership.Queries.query871_certified,N12Compact.HistoricalOwnership.Queries.query872_certified,N12Compact.HistoricalOwnership.Queries.query873_certified,N12Compact.HistoricalOwnership.Queries.query874_certified,N12Compact.HistoricalOwnership.Queries.query875_certified,N12Compact.HistoricalOwnership.Queries.query876_certified,N12Compact.HistoricalOwnership.Queries.query877_certified,N12Compact.HistoricalOwnership.Queries.query878_certified,N12Compact.HistoricalOwnership.Queries.query879_certified,N12Compact.HistoricalOwnership.Queries.query880_certified,N12Compact.HistoricalOwnership.Queries.query881_certified,N12Compact.HistoricalOwnership.Queries.query882_certified,N12Compact.HistoricalOwnership.Queries.query883_certified,N12Compact.HistoricalOwnership.Queries.query884_certified,N12Compact.HistoricalOwnership.Queries.query885_certified,N12Compact.HistoricalOwnership.Queries.query886_certified,N12Compact.HistoricalOwnership.Queries.query887_certified,N12Compact.HistoricalOwnership.Queries.query888_certified,N12Compact.HistoricalOwnership.Queries.query889_certified,N12Compact.HistoricalOwnership.Queries.query890_certified,N12Compact.HistoricalOwnership.Queries.query891_certified,N12Compact.HistoricalOwnership.Queries.query892_certified,N12Compact.HistoricalOwnership.Queries.query893_certified,N12Compact.HistoricalOwnership.Queries.query894_certified,N12Compact.HistoricalOwnership.Queries.query895_certified,N12Compact.HistoricalOwnership.Queries.query896_certified,N12Compact.HistoricalOwnership.Queries.query897_certified,N12Compact.HistoricalOwnership.Queries.query898_certified,N12Compact.HistoricalOwnership.Queries.query899_certified]⟩
private def single979_7_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(3072,1,{0}),(3072,1,{0,1}),(3072,1,{2}),(3072,1,{0,2}),(3072,1,{1,2}),(3072,1,{0,3}),(3072,1,{2,3}),(3072,1,{0,4}),(3072,1,{2,4}),(3072,1,{5}),(3072,1,{0,5}),(3072,1,{1,5}),(3072,1,{2,5}),(3072,1,{3,5}),(3072,1,{4,5}),(3072,1,{0,6}),(3072,1,{2,6}),(3072,1,{5,6}),(3072,1,{0,7}),(3072,1,{2,7}),(3072,1,{5,7}),(3072,1,{8}),(3072,1,{0,8}),(3072,1,{1,8}),(3072,1,{2,8}),(3072,1,{3,8}),(3072,1,{4,8}),(3072,1,{5,8}),(3072,1,{6,8}),(3072,1,{7,8}),(3072,1,{0,9}),(3072,1,{2,9}),(3072,1,{5,9}),(3072,1,{8,9})]
private theorem single979_7_1_queries_exact :
    single979_7_1Signatures = single979_7_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_7_1_queries_exact

private theorem single979_7_1_metadata :
    N12Compact.SmallOwnerDomain.Check single979_7_1 case979Family 1 single979_7_1Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨3072,0,2,[∅,{1},{3},{1,3},{4},{1,4},{3,4},{6},{1,6},{3,6},{4,6},{7},{1,7},{3,7},{4,7},{6,7},{9},{1,9},{3,9},{4,9},{6,9},{7,9}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_7_1Signatures
  decide +kernel
#check single979_7_1_metadata

theorem single979_7_1_checked : single979_7_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomain.checked single979_7_1 case979Family 1
    single979_7_1Signatures single979_7_1_queries_exact (by decide) single979_7_1_metadata

end
end S12

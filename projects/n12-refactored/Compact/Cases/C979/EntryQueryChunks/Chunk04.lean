import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_2_0 : DirectSingleDomain := ⟨12,0,1,[∅,{6},{8}],[N12Compact.HistoricalOwnership.Queries.query0_certified,N12Compact.HistoricalOwnership.Queries.query1_certified,N12Compact.HistoricalOwnership.Queries.query2_certified,N12Compact.HistoricalOwnership.Queries.query3_certified,N12Compact.HistoricalOwnership.Queries.query4_certified,N12Compact.HistoricalOwnership.Queries.query5_certified,N12Compact.HistoricalOwnership.Queries.query6_certified,N12Compact.HistoricalOwnership.Queries.query7_certified]⟩
private def single979_2_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(12,0,{0}),(12,0,{1}),(12,0,{2}),(12,0,{3}),(12,0,{4}),(12,0,{5}),(12,0,{7}),(12,0,{9})]
private theorem single979_2_0_queries_exact :
    single979_2_0Signatures = single979_2_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_2_0_queries_exact

private theorem single979_2_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_2_0 case979Family 0 single979_2_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨12,0,1,[∅,{6},{8}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_2_0Signatures
  decide +kernel
#check single979_2_0_metadata

theorem single979_2_0_checked : single979_2_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_2_0 case979Family 0
    single979_2_0Signatures single979_2_0_queries_exact (by decide) single979_2_0_metadata

end
end S12

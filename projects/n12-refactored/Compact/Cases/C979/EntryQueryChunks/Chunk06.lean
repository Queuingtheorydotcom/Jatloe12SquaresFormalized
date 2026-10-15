import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_3_0 : DirectSingleDomain := ⟨48,0,1,[∅,{7},{9}],[N12Compact.HistoricalOwnership.Queries.query1387_certified,N12Compact.HistoricalOwnership.Queries.query1388_certified,N12Compact.HistoricalOwnership.Queries.query1389_certified,N12Compact.HistoricalOwnership.Queries.query1390_certified,N12Compact.HistoricalOwnership.Queries.query1391_certified,N12Compact.HistoricalOwnership.Queries.query1392_certified,N12Compact.HistoricalOwnership.Queries.query1393_certified,N12Compact.HistoricalOwnership.Queries.query1394_certified]⟩
private def single979_3_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(48,0,{0}),(48,0,{1}),(48,0,{2}),(48,0,{3}),(48,0,{4}),(48,0,{5}),(48,0,{6}),(48,0,{8})]
private theorem single979_3_0_queries_exact :
    single979_3_0Signatures = single979_3_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_3_0_queries_exact

private theorem single979_3_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_3_0 case979Family 0 single979_3_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨48,0,1,[∅,{7},{9}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_3_0Signatures
  decide +kernel
#check single979_3_0_metadata

theorem single979_3_0_checked : single979_3_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_3_0 case979Family 0
    single979_3_0Signatures single979_3_0_queries_exact (by decide) single979_3_0_metadata

end
end S12

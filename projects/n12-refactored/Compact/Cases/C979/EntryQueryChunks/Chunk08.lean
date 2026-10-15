import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_4_0 : DirectSingleDomain := ⟨192,0,1,[∅,{1},{3}],[N12Compact.HistoricalOwnership.Queries.query53_certified,N12Compact.HistoricalOwnership.Queries.query54_certified,N12Compact.HistoricalOwnership.Queries.query55_certified,N12Compact.HistoricalOwnership.Queries.query56_certified,N12Compact.HistoricalOwnership.Queries.query57_certified,N12Compact.HistoricalOwnership.Queries.query58_certified,N12Compact.HistoricalOwnership.Queries.query59_certified,N12Compact.HistoricalOwnership.Queries.query60_certified]⟩
private def single979_4_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(192,0,{0}),(192,0,{2}),(192,0,{4}),(192,0,{5}),(192,0,{6}),(192,0,{7}),(192,0,{8}),(192,0,{9})]
private theorem single979_4_0_queries_exact :
    single979_4_0Signatures = single979_4_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_4_0_queries_exact

private theorem single979_4_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_4_0 case979Family 0 single979_4_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨192,0,1,[∅,{1},{3}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_4_0Signatures
  decide +kernel
#check single979_4_0_metadata

theorem single979_4_0_checked : single979_4_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_4_0 case979Family 0
    single979_4_0Signatures single979_4_0_queries_exact (by decide) single979_4_0_metadata

end
end S12

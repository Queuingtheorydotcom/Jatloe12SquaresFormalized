import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_0_0 : DirectSingleDomain := ⟨1,1,2,[{2}],[N12Compact.C979SharedSelections.selected0,N12Compact.C979SharedSelections.selected1,N12Compact.C979SharedSelections.selected2,N12Compact.C979SharedSelections.selected3,N12Compact.C979SharedSelections.selected4,N12Compact.C979SharedSelections.selected5,N12Compact.C979SharedSelections.selected6,N12Compact.C979SharedSelections.selected7,N12Compact.C979SharedSelections.selected8,N12Compact.C979SharedSelections.selected9,N12Compact.C979SharedSelections.selected10,N12Compact.C979SharedSelections.selected11,N12Compact.C979SharedSelections.selected12,N12Compact.C979SharedSelections.selected13,N12Compact.C979SharedSelections.selected14,N12Compact.C979SharedSelections.selected15,N12Compact.C979SharedSelections.selected16,N12Compact.C979SharedSelections.selected17,N12Compact.C979SharedSelections.selected18,N12Compact.C979SharedSelections.selected19,N12Compact.C979SharedSelections.selected20,N12Compact.C979SharedSelections.selected21,N12Compact.C979SharedSelections.selected22,N12Compact.C979SharedSelections.selected23,N12Compact.C979SharedSelections.selected24,N12Compact.C979SharedSelections.selected25,N12Compact.C979SharedSelections.selected26,N12Compact.C979SharedSelections.selected27,N12Compact.C979SharedSelections.selected28,N12Compact.C979SharedSelections.selected29,N12Compact.C979SharedSelections.selected30,N12Compact.C979SharedSelections.selected31,N12Compact.C979SharedSelections.selected32,N12Compact.C979SharedSelections.selected33,N12Compact.C979SharedSelections.selected34,N12Compact.C979SharedSelections.selected35,N12Compact.C979SharedSelections.selected36,N12Compact.C979SharedSelections.selected37,N12Compact.C979SharedSelections.selected38,N12Compact.C979SharedSelections.selected39,N12Compact.C979SharedSelections.selected40,N12Compact.C979SharedSelections.selected41,N12Compact.C979SharedSelections.selected42,N12Compact.C979SharedSelections.selected43,N12Compact.C979SharedSelections.selected44,N12Compact.C979SharedSelections.selected45,N12Compact.C979SharedSelections.selected46,N12Compact.C979SharedSelections.selected47,N12Compact.C979SharedSelections.selected48,N12Compact.C979SharedSelections.selected49,N12Compact.C979SharedSelections.selected50,N12Compact.C979SharedSelections.selected51,N12Compact.C979SharedSelections.selected52,N12Compact.C979SharedSelections.selected53]⟩
private def single979_0_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1,0,{0}),(1,0,{1}),(1,0,{0,1}),(1,0,{0,2}),(1,0,{1,2}),(1,0,{3}),(1,0,{0,3}),(1,0,{1,3}),(1,0,{2,3}),(1,0,{4}),(1,0,{0,4}),(1,0,{1,4}),(1,0,{2,4}),(1,0,{3,4}),(1,0,{5}),(1,0,{0,5}),(1,0,{1,5}),(1,0,{2,5}),(1,0,{3,5}),(1,0,{4,5}),(1,0,{6}),(1,0,{0,6}),(1,0,{1,6}),(1,0,{2,6}),(1,0,{3,6}),(1,0,{4,6}),(1,0,{5,6}),(1,0,{7}),(1,0,{0,7}),(1,0,{1,7}),(1,0,{2,7}),(1,0,{3,7}),(1,0,{4,7}),(1,0,{5,7}),(1,0,{6,7}),(1,0,{8}),(1,0,{0,8}),(1,0,{1,8}),(1,0,{2,8}),(1,0,{3,8}),(1,0,{4,8}),(1,0,{5,8}),(1,0,{6,8}),(1,0,{7,8}),(1,0,{9}),(1,0,{0,9}),(1,0,{1,9}),(1,0,{2,9}),(1,0,{3,9}),(1,0,{4,9}),(1,0,{5,9}),(1,0,{6,9}),(1,0,{7,9}),(1,0,{8,9})]
private theorem single979_0_0_queries_exact :
    single979_0_0Signatures = single979_0_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_0_0_queries_exact

private theorem single979_0_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_0_0 case979Family 0 single979_0_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨1,1,2,[{2}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_0_0Signatures
  decide +kernel
#check single979_0_0_metadata

theorem single979_0_0_checked : single979_0_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_0_0 case979Family 0
    single979_0_0Signatures single979_0_0_queries_exact (by decide) single979_0_0_metadata

end
end S12

import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_6_0 : DirectSingleDomain := ⟨512,1,2,[{4},{2,4},{4,5},{6},{4,6},{8},{4,8},{5,8},{6,8},{4,9},{8,9}],[N12Compact.C979SharedSelections.selected582,N12Compact.C979SharedSelections.selected583,N12Compact.C979SharedSelections.selected584,N12Compact.C979SharedSelections.selected585,N12Compact.C979SharedSelections.selected586,N12Compact.C979SharedSelections.selected587,N12Compact.C979SharedSelections.selected588,N12Compact.C979SharedSelections.selected589,N12Compact.C979SharedSelections.selected590,N12Compact.C979SharedSelections.selected591,N12Compact.C979SharedSelections.selected592,N12Compact.C979SharedSelections.selected593,N12Compact.C979SharedSelections.selected594,N12Compact.C979SharedSelections.selected595,N12Compact.C979SharedSelections.selected596,N12Compact.C979SharedSelections.selected597,N12Compact.C979SharedSelections.selected598,N12Compact.C979SharedSelections.selected599,N12Compact.C979SharedSelections.selected600,N12Compact.C979SharedSelections.selected601,N12Compact.C979SharedSelections.selected602,N12Compact.C979SharedSelections.selected603,N12Compact.C979SharedSelections.selected604,N12Compact.C979SharedSelections.selected605,N12Compact.C979SharedSelections.selected606,N12Compact.C979SharedSelections.selected607,N12Compact.C979SharedSelections.selected608,N12Compact.C979SharedSelections.selected609,N12Compact.C979SharedSelections.selected610,N12Compact.C979SharedSelections.selected611,N12Compact.C979SharedSelections.selected612,N12Compact.C979SharedSelections.selected613,N12Compact.C979SharedSelections.selected614,N12Compact.C979SharedSelections.selected615,N12Compact.C979SharedSelections.selected616,N12Compact.C979SharedSelections.selected617,N12Compact.C979SharedSelections.selected618,N12Compact.C979SharedSelections.selected619,N12Compact.C979SharedSelections.selected620,N12Compact.C979SharedSelections.selected621,N12Compact.C979SharedSelections.selected622,N12Compact.C979SharedSelections.selected623,N12Compact.C979SharedSelections.selected624,N12Compact.C979SharedSelections.selected625]⟩
private def single979_6_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(512,0,{0}),(512,0,{1}),(512,0,{0,1}),(512,0,{2}),(512,0,{0,2}),(512,0,{1,2}),(512,0,{3}),(512,0,{0,3}),(512,0,{1,3}),(512,0,{2,3}),(512,0,{0,4}),(512,0,{1,4}),(512,0,{3,4}),(512,0,{5}),(512,0,{0,5}),(512,0,{1,5}),(512,0,{2,5}),(512,0,{3,5}),(512,0,{0,6}),(512,0,{1,6}),(512,0,{2,6}),(512,0,{3,6}),(512,0,{5,6}),(512,0,{7}),(512,0,{0,7}),(512,0,{1,7}),(512,0,{2,7}),(512,0,{3,7}),(512,0,{4,7}),(512,0,{5,7}),(512,0,{6,7}),(512,0,{0,8}),(512,0,{1,8}),(512,0,{2,8}),(512,0,{3,8}),(512,0,{7,8}),(512,0,{9}),(512,0,{0,9}),(512,0,{1,9}),(512,0,{2,9}),(512,0,{3,9}),(512,0,{5,9}),(512,0,{6,9}),(512,0,{7,9})]
private theorem single979_6_0_queries_exact :
    single979_6_0Signatures = single979_6_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_6_0_queries_exact

private theorem single979_6_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_6_0 case979Family 0 single979_6_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨512,1,2,[{4},{2,4},{4,5},{6},{4,6},{8},{4,8},{5,8},{6,8},{4,9},{8,9}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_6_0Signatures
  decide +kernel
#check single979_6_0_metadata

theorem single979_6_0_checked : single979_6_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_6_0 case979Family 0
    single979_6_0Signatures single979_6_0_queries_exact (by decide) single979_6_0_metadata

end
end S12

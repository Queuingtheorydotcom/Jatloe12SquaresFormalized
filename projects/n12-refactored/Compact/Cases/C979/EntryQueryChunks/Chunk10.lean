import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_5_0 : DirectSingleDomain := ⟨256,1,2,[{0},{0,1},{2},{0,2},{4},{0,4},{1,4},{2,4},{0,5},{4,5},{4,6}],[N12Compact.C979SharedSelections.selected429,N12Compact.C979SharedSelections.selected430,N12Compact.C979SharedSelections.selected431,N12Compact.C979SharedSelections.selected432,N12Compact.C979SharedSelections.selected433,N12Compact.C979SharedSelections.selected434,N12Compact.C979SharedSelections.selected435,N12Compact.C979SharedSelections.selected436,N12Compact.C979SharedSelections.selected437,N12Compact.C979SharedSelections.selected438,N12Compact.C979SharedSelections.selected439,N12Compact.C979SharedSelections.selected440,N12Compact.C979SharedSelections.selected441,N12Compact.C979SharedSelections.selected442,N12Compact.C979SharedSelections.selected443,N12Compact.C979SharedSelections.selected444,N12Compact.C979SharedSelections.selected445,N12Compact.C979SharedSelections.selected446,N12Compact.C979SharedSelections.selected447,N12Compact.C979SharedSelections.selected448,N12Compact.C979SharedSelections.selected449,N12Compact.C979SharedSelections.selected450,N12Compact.C979SharedSelections.selected451,N12Compact.C979SharedSelections.selected452,N12Compact.C979SharedSelections.selected453,N12Compact.C979SharedSelections.selected454,N12Compact.C979SharedSelections.selected455,N12Compact.C979SharedSelections.selected456,N12Compact.C979SharedSelections.selected457,N12Compact.C979SharedSelections.selected458,N12Compact.C979SharedSelections.selected459,N12Compact.C979SharedSelections.selected460,N12Compact.C979SharedSelections.selected461,N12Compact.C979SharedSelections.selected462,N12Compact.C979SharedSelections.selected463,N12Compact.C979SharedSelections.selected464,N12Compact.C979SharedSelections.selected465,N12Compact.C979SharedSelections.selected466,N12Compact.C979SharedSelections.selected467,N12Compact.C979SharedSelections.selected468,N12Compact.C979SharedSelections.selected469,N12Compact.C979SharedSelections.selected470,N12Compact.C979SharedSelections.selected471,N12Compact.C979SharedSelections.selected472]⟩
private def single979_5_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(256,0,{1}),(256,0,{1,2}),(256,0,{3}),(256,0,{0,3}),(256,0,{1,3}),(256,0,{2,3}),(256,0,{3,4}),(256,0,{5}),(256,0,{1,5}),(256,0,{2,5}),(256,0,{3,5}),(256,0,{6}),(256,0,{0,6}),(256,0,{1,6}),(256,0,{2,6}),(256,0,{3,6}),(256,0,{5,6}),(256,0,{7}),(256,0,{0,7}),(256,0,{1,7}),(256,0,{2,7}),(256,0,{3,7}),(256,0,{4,7}),(256,0,{5,7}),(256,0,{6,7}),(256,0,{8}),(256,0,{0,8}),(256,0,{1,8}),(256,0,{2,8}),(256,0,{3,8}),(256,0,{4,8}),(256,0,{5,8}),(256,0,{6,8}),(256,0,{7,8}),(256,0,{9}),(256,0,{0,9}),(256,0,{1,9}),(256,0,{2,9}),(256,0,{3,9}),(256,0,{4,9}),(256,0,{5,9}),(256,0,{6,9}),(256,0,{7,9}),(256,0,{8,9})]
private theorem single979_5_0_queries_exact :
    single979_5_0Signatures = single979_5_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_5_0_queries_exact

private theorem single979_5_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_5_0 case979Family 0 single979_5_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨256,1,2,[{0},{0,1},{2},{0,2},{4},{0,4},{1,4},{2,4},{0,5},{4,5},{4,6}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_5_0Signatures
  decide +kernel
#check single979_5_0_metadata

theorem single979_5_0_checked : single979_5_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_5_0 case979Family 0
    single979_5_0Signatures single979_5_0_queries_exact (by decide) single979_5_0_metadata

end
end S12

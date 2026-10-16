import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_1_0 : DirectSingleDomain := ⟨2,1,2,[{0},{0,2}],[N12Compact.C979SharedSelections.selected107,N12Compact.C979SharedSelections.selected108,N12Compact.C979SharedSelections.selected109,N12Compact.C979SharedSelections.selected110,N12Compact.C979SharedSelections.selected111,N12Compact.C979SharedSelections.selected112,N12Compact.C979SharedSelections.selected113,N12Compact.C979SharedSelections.selected114,N12Compact.C979SharedSelections.selected115,N12Compact.C979SharedSelections.selected116,N12Compact.C979SharedSelections.selected117,N12Compact.C979SharedSelections.selected118,N12Compact.C979SharedSelections.selected119,N12Compact.C979SharedSelections.selected120,N12Compact.C979SharedSelections.selected121,N12Compact.C979SharedSelections.selected122,N12Compact.C979SharedSelections.selected123,N12Compact.C979SharedSelections.selected124,N12Compact.C979SharedSelections.selected125,N12Compact.C979SharedSelections.selected126,N12Compact.C979SharedSelections.selected127,N12Compact.C979SharedSelections.selected128,N12Compact.C979SharedSelections.selected129,N12Compact.C979SharedSelections.selected130,N12Compact.C979SharedSelections.selected131,N12Compact.C979SharedSelections.selected132,N12Compact.C979SharedSelections.selected133,N12Compact.C979SharedSelections.selected134,N12Compact.C979SharedSelections.selected135,N12Compact.C979SharedSelections.selected136,N12Compact.C979SharedSelections.selected137,N12Compact.C979SharedSelections.selected138,N12Compact.C979SharedSelections.selected139,N12Compact.C979SharedSelections.selected140,N12Compact.C979SharedSelections.selected141,N12Compact.C979SharedSelections.selected142,N12Compact.C979SharedSelections.selected143,N12Compact.C979SharedSelections.selected144,N12Compact.C979SharedSelections.selected145,N12Compact.C979SharedSelections.selected146,N12Compact.C979SharedSelections.selected147,N12Compact.C979SharedSelections.selected148,N12Compact.C979SharedSelections.selected149,N12Compact.C979SharedSelections.selected150,N12Compact.C979SharedSelections.selected151,N12Compact.C979SharedSelections.selected152,N12Compact.C979SharedSelections.selected153,N12Compact.C979SharedSelections.selected154,N12Compact.C979SharedSelections.selected155,N12Compact.C979SharedSelections.selected156,N12Compact.C979SharedSelections.selected157,N12Compact.C979SharedSelections.selected158,N12Compact.C979SharedSelections.selected159]⟩
private def single979_1_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(2,0,{1}),(2,0,{0,1}),(2,0,{2}),(2,0,{1,2}),(2,0,{3}),(2,0,{0,3}),(2,0,{1,3}),(2,0,{2,3}),(2,0,{4}),(2,0,{0,4}),(2,0,{1,4}),(2,0,{2,4}),(2,0,{3,4}),(2,0,{5}),(2,0,{0,5}),(2,0,{1,5}),(2,0,{2,5}),(2,0,{3,5}),(2,0,{4,5}),(2,0,{6}),(2,0,{0,6}),(2,0,{1,6}),(2,0,{2,6}),(2,0,{3,6}),(2,0,{4,6}),(2,0,{5,6}),(2,0,{7}),(2,0,{0,7}),(2,0,{1,7}),(2,0,{2,7}),(2,0,{3,7}),(2,0,{4,7}),(2,0,{5,7}),(2,0,{6,7}),(2,0,{8}),(2,0,{0,8}),(2,0,{1,8}),(2,0,{2,8}),(2,0,{3,8}),(2,0,{4,8}),(2,0,{5,8}),(2,0,{6,8}),(2,0,{7,8}),(2,0,{9}),(2,0,{0,9}),(2,0,{1,9}),(2,0,{2,9}),(2,0,{3,9}),(2,0,{4,9}),(2,0,{5,9}),(2,0,{6,9}),(2,0,{7,9}),(2,0,{8,9})]
private theorem single979_1_0_queries_exact :
    single979_1_0Signatures = single979_1_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_1_0_queries_exact

private theorem single979_1_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_1_0 case979Family 0 single979_1_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨2,1,2,[{0},{0,2}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_1_0Signatures
  decide +kernel
#check single979_1_0_metadata

theorem single979_1_0_checked : single979_1_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_1_0 case979Family 0
    single979_1_0Signatures single979_1_0_queries_exact (by decide) single979_1_0_metadata

end
end S12

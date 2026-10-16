import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_8_0 : DirectSingleDomain := ⟨4096,1,2,[{0},{1},{0,1},{0,2},{1,3}],[N12Compact.C979SharedSelections.selected989,N12Compact.C979SharedSelections.selected990,N12Compact.C979SharedSelections.selected991,N12Compact.C979SharedSelections.selected992,N12Compact.C979SharedSelections.selected993,N12Compact.C979SharedSelections.selected994,N12Compact.C979SharedSelections.selected995,N12Compact.C979SharedSelections.selected996,N12Compact.C979SharedSelections.selected997,N12Compact.C979SharedSelections.selected998,N12Compact.C979SharedSelections.selected999,N12Compact.C979SharedSelections.selected1000,N12Compact.C979SharedSelections.selected1001,N12Compact.C979SharedSelections.selected1002,N12Compact.C979SharedSelections.selected1003,N12Compact.C979SharedSelections.selected1004,N12Compact.C979SharedSelections.selected1005,N12Compact.C979SharedSelections.selected1006,N12Compact.C979SharedSelections.selected1007,N12Compact.C979SharedSelections.selected1008,N12Compact.C979SharedSelections.selected1009,N12Compact.C979SharedSelections.selected1010,N12Compact.C979SharedSelections.selected1011,N12Compact.C979SharedSelections.selected1012,N12Compact.C979SharedSelections.selected1013,N12Compact.C979SharedSelections.selected1014,N12Compact.C979SharedSelections.selected1015,N12Compact.C979SharedSelections.selected1016,N12Compact.C979SharedSelections.selected1017,N12Compact.C979SharedSelections.selected1018,N12Compact.C979SharedSelections.selected1019,N12Compact.C979SharedSelections.selected1020,N12Compact.C979SharedSelections.selected1021,N12Compact.C979SharedSelections.selected1022,N12Compact.C979SharedSelections.selected1023,N12Compact.C979SharedSelections.selected1024,N12Compact.C979SharedSelections.selected1025,N12Compact.C979SharedSelections.selected1026,N12Compact.C979SharedSelections.selected1027,N12Compact.C979SharedSelections.selected1028,N12Compact.C979SharedSelections.selected1029,N12Compact.C979SharedSelections.selected1030,N12Compact.C979SharedSelections.selected1031,N12Compact.C979SharedSelections.selected1032,N12Compact.C979SharedSelections.selected1033,N12Compact.C979SharedSelections.selected1034,N12Compact.C979SharedSelections.selected1035,N12Compact.C979SharedSelections.selected1036,N12Compact.C979SharedSelections.selected1037,N12Compact.C979SharedSelections.selected1038]⟩
private def single979_8_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(4096,0,{2}),(4096,0,{1,2}),(4096,0,{3}),(4096,0,{0,3}),(4096,0,{2,3}),(4096,0,{4}),(4096,0,{0,4}),(4096,0,{1,4}),(4096,0,{2,4}),(4096,0,{3,4}),(4096,0,{5}),(4096,0,{0,5}),(4096,0,{1,5}),(4096,0,{2,5}),(4096,0,{3,5}),(4096,0,{4,5}),(4096,0,{6}),(4096,0,{0,6}),(4096,0,{1,6}),(4096,0,{2,6}),(4096,0,{3,6}),(4096,0,{4,6}),(4096,0,{5,6}),(4096,0,{7}),(4096,0,{0,7}),(4096,0,{1,7}),(4096,0,{2,7}),(4096,0,{3,7}),(4096,0,{4,7}),(4096,0,{5,7}),(4096,0,{6,7}),(4096,0,{8}),(4096,0,{0,8}),(4096,0,{1,8}),(4096,0,{2,8}),(4096,0,{3,8}),(4096,0,{4,8}),(4096,0,{5,8}),(4096,0,{6,8}),(4096,0,{7,8}),(4096,0,{9}),(4096,0,{0,9}),(4096,0,{1,9}),(4096,0,{2,9}),(4096,0,{3,9}),(4096,0,{4,9}),(4096,0,{5,9}),(4096,0,{6,9}),(4096,0,{7,9}),(4096,0,{8,9})]
private theorem single979_8_0_queries_exact :
    single979_8_0Signatures = single979_8_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_8_0_queries_exact

private theorem single979_8_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_8_0 case979Family 0 single979_8_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨4096,1,2,[{0},{1},{0,1},{0,2},{1,3}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_8_0Signatures
  decide +kernel
#check single979_8_0_metadata

theorem single979_8_0_checked : single979_8_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_8_0 case979Family 0
    single979_8_0Signatures single979_8_0_queries_exact (by decide) single979_8_0_metadata

end
end S12

import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_9_0 : DirectSingleDomain := ⟨8192,1,2,[{2},{4},{2,4},{6},{2,6},{4,6}],[N12Compact.C979SharedSelections.selected1145,N12Compact.C979SharedSelections.selected1146,N12Compact.C979SharedSelections.selected1147,N12Compact.C979SharedSelections.selected1148,N12Compact.C979SharedSelections.selected1149,N12Compact.C979SharedSelections.selected1150,N12Compact.C979SharedSelections.selected1151,N12Compact.C979SharedSelections.selected1152,N12Compact.C979SharedSelections.selected1153,N12Compact.C979SharedSelections.selected1154,N12Compact.C979SharedSelections.selected1155,N12Compact.C979SharedSelections.selected1156,N12Compact.C979SharedSelections.selected1157,N12Compact.C979SharedSelections.selected1158,N12Compact.C979SharedSelections.selected1159,N12Compact.C979SharedSelections.selected1160,N12Compact.C979SharedSelections.selected1161,N12Compact.C979SharedSelections.selected1162,N12Compact.C979SharedSelections.selected1163,N12Compact.C979SharedSelections.selected1164,N12Compact.C979SharedSelections.selected1165,N12Compact.C979SharedSelections.selected1166,N12Compact.C979SharedSelections.selected1167,N12Compact.C979SharedSelections.selected1168,N12Compact.C979SharedSelections.selected1169,N12Compact.C979SharedSelections.selected1170,N12Compact.C979SharedSelections.selected1171,N12Compact.C979SharedSelections.selected1172,N12Compact.C979SharedSelections.selected1173,N12Compact.C979SharedSelections.selected1174,N12Compact.C979SharedSelections.selected1175,N12Compact.C979SharedSelections.selected1176,N12Compact.C979SharedSelections.selected1177,N12Compact.C979SharedSelections.selected1178,N12Compact.C979SharedSelections.selected1179,N12Compact.C979SharedSelections.selected1180,N12Compact.C979SharedSelections.selected1181,N12Compact.C979SharedSelections.selected1182,N12Compact.C979SharedSelections.selected1183,N12Compact.C979SharedSelections.selected1184,N12Compact.C979SharedSelections.selected1185,N12Compact.C979SharedSelections.selected1186,N12Compact.C979SharedSelections.selected1187,N12Compact.C979SharedSelections.selected1188,N12Compact.C979SharedSelections.selected1189,N12Compact.C979SharedSelections.selected1190,N12Compact.C979SharedSelections.selected1191,N12Compact.C979SharedSelections.selected1192,N12Compact.C979SharedSelections.selected1193]⟩
private def single979_9_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(8192,0,{0}),(8192,0,{1}),(8192,0,{0,1}),(8192,0,{0,2}),(8192,0,{1,2}),(8192,0,{3}),(8192,0,{0,3}),(8192,0,{1,3}),(8192,0,{2,3}),(8192,0,{0,4}),(8192,0,{1,4}),(8192,0,{3,4}),(8192,0,{5}),(8192,0,{0,5}),(8192,0,{1,5}),(8192,0,{2,5}),(8192,0,{3,5}),(8192,0,{4,5}),(8192,0,{0,6}),(8192,0,{1,6}),(8192,0,{3,6}),(8192,0,{5,6}),(8192,0,{7}),(8192,0,{0,7}),(8192,0,{1,7}),(8192,0,{2,7}),(8192,0,{3,7}),(8192,0,{4,7}),(8192,0,{5,7}),(8192,0,{6,7}),(8192,0,{8}),(8192,0,{0,8}),(8192,0,{1,8}),(8192,0,{2,8}),(8192,0,{3,8}),(8192,0,{4,8}),(8192,0,{5,8}),(8192,0,{6,8}),(8192,0,{7,8}),(8192,0,{9}),(8192,0,{0,9}),(8192,0,{1,9}),(8192,0,{2,9}),(8192,0,{3,9}),(8192,0,{4,9}),(8192,0,{5,9}),(8192,0,{6,9}),(8192,0,{7,9}),(8192,0,{8,9})]
private theorem single979_9_0_queries_exact :
    single979_9_0Signatures = single979_9_0.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_9_0_queries_exact

private theorem single979_9_0_metadata :
    N12Compact.SmallOwnerDomain.Check single979_9_0 case979Family 0 single979_9_0Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨8192,1,2,[{2},{4},{2,4},{6},{2,6},{4,6}],[]⟩ : DirectSingleDomain)
    case979Family 0 single979_9_0Signatures
  decide +kernel
#check single979_9_0_metadata

theorem single979_9_0_checked : single979_9_0.Check case979Family 0 :=
  N12Compact.SmallOwnerDomain.checked single979_9_0 case979Family 0
    single979_9_0Signatures single979_9_0_queries_exact (by decide) single979_9_0_metadata

end
end S12

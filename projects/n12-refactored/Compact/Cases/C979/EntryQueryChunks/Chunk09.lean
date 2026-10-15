import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_4_1 : DirectSingleDomain := ⟨192,0,2,[∅,{1},{4},{1,4}],[N12Compact.HistoricalOwnership.Queries.query769_certified,N12Compact.HistoricalOwnership.Queries.query770_certified,N12Compact.HistoricalOwnership.Queries.query771_certified,N12Compact.HistoricalOwnership.Queries.query772_certified,N12Compact.HistoricalOwnership.Queries.query773_certified,N12Compact.HistoricalOwnership.Queries.query774_certified,N12Compact.HistoricalOwnership.Queries.query775_certified,N12Compact.HistoricalOwnership.Queries.query776_certified,N12Compact.HistoricalOwnership.Queries.query777_certified,N12Compact.HistoricalOwnership.Queries.query778_certified,N12Compact.HistoricalOwnership.Queries.query779_certified,N12Compact.HistoricalOwnership.Queries.query780_certified,N12Compact.HistoricalOwnership.Queries.query781_certified,N12Compact.HistoricalOwnership.Queries.query782_certified,N12Compact.HistoricalOwnership.Queries.query783_certified,N12Compact.HistoricalOwnership.Queries.query784_certified,N12Compact.HistoricalOwnership.Queries.query785_certified,N12Compact.HistoricalOwnership.Queries.query786_certified,N12Compact.HistoricalOwnership.Queries.query787_certified,N12Compact.HistoricalOwnership.Queries.query788_certified,N12Compact.HistoricalOwnership.Queries.query789_certified,N12Compact.HistoricalOwnership.Queries.query790_certified,N12Compact.HistoricalOwnership.Queries.query791_certified,N12Compact.HistoricalOwnership.Queries.query792_certified,N12Compact.HistoricalOwnership.Queries.query793_certified,N12Compact.HistoricalOwnership.Queries.query794_certified,N12Compact.HistoricalOwnership.Queries.query795_certified,N12Compact.HistoricalOwnership.Queries.query796_certified,N12Compact.HistoricalOwnership.Queries.query797_certified,N12Compact.HistoricalOwnership.Queries.query798_certified,N12Compact.HistoricalOwnership.Queries.query799_certified,N12Compact.HistoricalOwnership.Queries.query800_certified,N12Compact.HistoricalOwnership.Queries.query801_certified,N12Compact.HistoricalOwnership.Queries.query802_certified,N12Compact.HistoricalOwnership.Queries.query803_certified,N12Compact.HistoricalOwnership.Queries.query804_certified,N12Compact.HistoricalOwnership.Queries.query805_certified,N12Compact.HistoricalOwnership.Queries.query806_certified,N12Compact.HistoricalOwnership.Queries.query807_certified,N12Compact.HistoricalOwnership.Queries.query808_certified,N12Compact.HistoricalOwnership.Queries.query809_certified,N12Compact.HistoricalOwnership.Queries.query810_certified,N12Compact.HistoricalOwnership.Queries.query811_certified,N12Compact.HistoricalOwnership.Queries.query812_certified,N12Compact.HistoricalOwnership.Queries.query813_certified,N12Compact.HistoricalOwnership.Queries.query814_certified,N12Compact.HistoricalOwnership.Queries.query815_certified,N12Compact.HistoricalOwnership.Queries.query816_certified,N12Compact.HistoricalOwnership.Queries.query817_certified,N12Compact.HistoricalOwnership.Queries.query818_certified,N12Compact.HistoricalOwnership.Queries.query819_certified,N12Compact.HistoricalOwnership.Queries.query820_certified]⟩
private def single979_4_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(192,1,{0}),(192,1,{0,1}),(192,1,{2}),(192,1,{0,2}),(192,1,{1,2}),(192,1,{3}),(192,1,{0,3}),(192,1,{1,3}),(192,1,{2,3}),(192,1,{0,4}),(192,1,{2,4}),(192,1,{3,4}),(192,1,{5}),(192,1,{0,5}),(192,1,{1,5}),(192,1,{2,5}),(192,1,{3,5}),(192,1,{4,5}),(192,1,{6}),(192,1,{0,6}),(192,1,{1,6}),(192,1,{2,6}),(192,1,{3,6}),(192,1,{4,6}),(192,1,{5,6}),(192,1,{7}),(192,1,{0,7}),(192,1,{1,7}),(192,1,{2,7}),(192,1,{3,7}),(192,1,{4,7}),(192,1,{5,7}),(192,1,{6,7}),(192,1,{8}),(192,1,{0,8}),(192,1,{1,8}),(192,1,{2,8}),(192,1,{3,8}),(192,1,{4,8}),(192,1,{5,8}),(192,1,{6,8}),(192,1,{7,8}),(192,1,{9}),(192,1,{0,9}),(192,1,{1,9}),(192,1,{2,9}),(192,1,{3,9}),(192,1,{4,9}),(192,1,{5,9}),(192,1,{6,9}),(192,1,{7,9}),(192,1,{8,9})]
private theorem single979_4_1_queries_exact :
    single979_4_1Signatures = single979_4_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_4_1_queries_exact

private theorem single979_4_1_metadata :
    N12Compact.SmallOwnerDomain.Check single979_4_1 case979Family 1 single979_4_1Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨192,0,2,[∅,{1},{4},{1,4}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_4_1Signatures
  decide +kernel
#check single979_4_1_metadata

theorem single979_4_1_checked : single979_4_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomain.checked single979_4_1 case979Family 1
    single979_4_1Signatures single979_4_1_queries_exact (by decide) single979_4_1_metadata

end
end S12

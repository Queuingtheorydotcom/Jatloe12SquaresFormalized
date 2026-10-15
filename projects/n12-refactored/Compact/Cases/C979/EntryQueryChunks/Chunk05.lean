import Compact.Cases.C979.SharedSelections.Chunk49

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single979_2_1 : DirectSingleDomain := ⟨12,0,2,[∅,{5},{8},{5,8}],[N12Compact.HistoricalOwnership.Queries.query386_certified,N12Compact.HistoricalOwnership.Queries.query387_certified,N12Compact.HistoricalOwnership.Queries.query388_certified,N12Compact.HistoricalOwnership.Queries.query389_certified,N12Compact.HistoricalOwnership.Queries.query390_certified,N12Compact.HistoricalOwnership.Queries.query391_certified,N12Compact.HistoricalOwnership.Queries.query392_certified,N12Compact.HistoricalOwnership.Queries.query393_certified,N12Compact.HistoricalOwnership.Queries.query394_certified,N12Compact.HistoricalOwnership.Queries.query395_certified,N12Compact.HistoricalOwnership.Queries.query396_certified,N12Compact.HistoricalOwnership.Queries.query397_certified,N12Compact.HistoricalOwnership.Queries.query398_certified,N12Compact.HistoricalOwnership.Queries.query399_certified,N12Compact.HistoricalOwnership.Queries.query400_certified,N12Compact.HistoricalOwnership.Queries.query401_certified,N12Compact.HistoricalOwnership.Queries.query402_certified,N12Compact.HistoricalOwnership.Queries.query403_certified,N12Compact.HistoricalOwnership.Queries.query404_certified,N12Compact.HistoricalOwnership.Queries.query405_certified,N12Compact.HistoricalOwnership.Queries.query406_certified,N12Compact.HistoricalOwnership.Queries.query407_certified,N12Compact.HistoricalOwnership.Queries.query408_certified,N12Compact.HistoricalOwnership.Queries.query409_certified,N12Compact.HistoricalOwnership.Queries.query410_certified,N12Compact.HistoricalOwnership.Queries.query411_certified,N12Compact.HistoricalOwnership.Queries.query412_certified,N12Compact.HistoricalOwnership.Queries.query413_certified,N12Compact.HistoricalOwnership.Queries.query414_certified,N12Compact.HistoricalOwnership.Queries.query415_certified,N12Compact.HistoricalOwnership.Queries.query416_certified,N12Compact.HistoricalOwnership.Queries.query417_certified,N12Compact.HistoricalOwnership.Queries.query418_certified,N12Compact.HistoricalOwnership.Queries.query419_certified,N12Compact.HistoricalOwnership.Queries.query420_certified,N12Compact.HistoricalOwnership.Queries.query421_certified,N12Compact.HistoricalOwnership.Queries.query422_certified,N12Compact.HistoricalOwnership.Queries.query423_certified,N12Compact.HistoricalOwnership.Queries.query424_certified,N12Compact.HistoricalOwnership.Queries.query425_certified,N12Compact.HistoricalOwnership.Queries.query426_certified,N12Compact.HistoricalOwnership.Queries.query427_certified,N12Compact.HistoricalOwnership.Queries.query428_certified,N12Compact.HistoricalOwnership.Queries.query429_certified,N12Compact.HistoricalOwnership.Queries.query430_certified,N12Compact.HistoricalOwnership.Queries.query431_certified,N12Compact.HistoricalOwnership.Queries.query432_certified,N12Compact.HistoricalOwnership.Queries.query433_certified,N12Compact.HistoricalOwnership.Queries.query434_certified,N12Compact.HistoricalOwnership.Queries.query435_certified,N12Compact.HistoricalOwnership.Queries.query436_certified,N12Compact.HistoricalOwnership.Queries.query437_certified]⟩
private def single979_2_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(12,1,{0}),(12,1,{1}),(12,1,{0,1}),(12,1,{2}),(12,1,{0,2}),(12,1,{1,2}),(12,1,{3}),(12,1,{0,3}),(12,1,{1,3}),(12,1,{2,3}),(12,1,{4}),(12,1,{0,4}),(12,1,{1,4}),(12,1,{2,4}),(12,1,{3,4}),(12,1,{0,5}),(12,1,{1,5}),(12,1,{2,5}),(12,1,{3,5}),(12,1,{4,5}),(12,1,{6}),(12,1,{0,6}),(12,1,{1,6}),(12,1,{2,6}),(12,1,{3,6}),(12,1,{4,6}),(12,1,{5,6}),(12,1,{7}),(12,1,{0,7}),(12,1,{1,7}),(12,1,{2,7}),(12,1,{3,7}),(12,1,{4,7}),(12,1,{5,7}),(12,1,{6,7}),(12,1,{0,8}),(12,1,{1,8}),(12,1,{2,8}),(12,1,{3,8}),(12,1,{4,8}),(12,1,{6,8}),(12,1,{7,8}),(12,1,{9}),(12,1,{0,9}),(12,1,{1,9}),(12,1,{2,9}),(12,1,{3,9}),(12,1,{4,9}),(12,1,{5,9}),(12,1,{6,9}),(12,1,{7,9}),(12,1,{8,9})]
private theorem single979_2_1_queries_exact :
    single979_2_1Signatures = single979_2_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl
#check single979_2_1_queries_exact

private theorem single979_2_1_metadata :
    N12Compact.SmallOwnerDomain.Check single979_2_1 case979Family 1 single979_2_1Signatures := by
  change N12Compact.SmallOwnerDomain.Check (⟨12,0,2,[∅,{5},{8},{5,8}],[]⟩ : DirectSingleDomain)
    case979Family 1 single979_2_1Signatures
  decide +kernel
#check single979_2_1_metadata

theorem single979_2_1_checked : single979_2_1.Check case979Family 1 :=
  N12Compact.SmallOwnerDomain.checked single979_2_1 case979Family 1
    single979_2_1Signatures single979_2_1_queries_exact (by decide) single979_2_1_metadata

end
end S12

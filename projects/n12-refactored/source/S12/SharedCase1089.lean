import S12.Case1089To0Aux
namespace S12
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem case1089_shared_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=case1089Family) : False := by
 have he : case1089AuxRemaining0=[] := by native_decide
 have h := case1089_aux_reduction_to0 p hf
 rw [he] at h
 exact List.not_mem_nil h
#print axioms case1089_shared_impossible
end S12

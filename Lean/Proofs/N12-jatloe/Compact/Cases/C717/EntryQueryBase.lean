import S12.DirectSingleDomain
import S12.LocalQueryData

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def case717Family : Finset Nat := {1,2,12,16,32,192,768,3072,4096,8192,16384,32768}
theorem c717_query_at (queries : List LocalQuery)
    (checked : queries.all (fun w => decide w.Check) = true)
    (i : Fin queries.length) : (queries.get i).Check :=
  of_decide_eq_true (List.all_eq_true.mp checked _ (List.get_mem queries i))

end
end S12

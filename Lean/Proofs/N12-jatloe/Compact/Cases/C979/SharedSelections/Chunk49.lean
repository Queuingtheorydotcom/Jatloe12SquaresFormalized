import Compact.Cases.C979.SharedSelections.Chunk48

namespace N12Compact.C979SharedSelections
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable def selected1633 : {q : LocalQuery // q.Check} := (certified_query% 1633)

noncomputable def selected1634 : {q : LocalQuery // q.Check} := (certified_query% 1634)
end N12Compact.C979SharedSelections

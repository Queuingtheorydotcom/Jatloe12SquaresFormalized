import Compact.HistoricalData.SharedPoses
import Compact.Bridge.IndexedRelaxation
import S12.AngleData64
import S12.AngleData128

namespace N12Compact.C713Shared
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def angles (i : Fin 192) : {w : AngleEnclosure // w.Check} :=
  if i.val < 64 then (angles64[i.val]?).getD ⟨angle64_0,angle64_0_checked⟩
  else (angles128[i.val-64]?).getD ⟨angle128_0,angle128_0_checked⟩

def dictionary : IndexedRelaxation.Dictionary HistoricalData.rowCount HistoricalData.poseCount 192 :=
  ⟨HistoricalData.rows, HistoricalData.denominators, angles,
   HistoricalData.poseAngle, HistoricalData.poseRows⟩

def poses : Fin HistoricalData.poseCount → PoseLeaf := dictionary.pose

theorem angles128_cover_kernel : CoversInterval 0 1 (angles128.map Subtype.val) := by
  decide +kernel

end
end N12Compact.C713Shared

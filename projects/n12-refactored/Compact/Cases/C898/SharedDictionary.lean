import Compact.Cases.C898.SharedPoses
import Compact.Bridge.IndexedRelaxation

namespace N12Compact.C898Shared
open S12

noncomputable def dictionary : IndexedRelaxation.Dictionary rowCount poseCount 64 :=
  ⟨rows, denominators,
    fun i => (angles64[i.val]?).getD ⟨angle64_0, angle64_0_checked⟩,
    poseAngle, poseRows⟩

theorem dictionary_pose (i : Fin poseCount) : dictionary.pose i = poses i := rfl

end N12Compact.C898Shared

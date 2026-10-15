import Compact.Bridge.DirectRecipeTable
import Compact.Bridge.IndexedRelaxation

/-! Exact recipe banks for existing shared pose dictionaries.

This bridge is generic in the row storage, pose storage and angle grid.
Positive denominators recover the predecessor encoding without copying any
rows or assuming a new pose equality. It is shared by all case adapters.
-/

namespace N12Compact.DirectRecipeTable

open S12 DirectPoseCover IndexedRelaxation

def Bank.ofDictionary {rowCount poseCount angleCount : Nat}
    (dictionary : Dictionary rowCount poseCount angleCount)
    (positive : ∀ r, 0 < dictionary.denominators r) : Bank angleCount poseCount where
  angles := dictionary.angles
  poseAngle := dictionary.poseAngle
  forms i := (dictionary.poseRows i).map (fun r =>
    ⟨dictionary.rows r, dictionary.denominators r - 1⟩)
  poses := dictionary.pose
  pose_exact := by
    intro i
    apply congrArg (fun inputs =>
      (⟨dictionary.angles (dictionary.poseAngle i), inputs⟩ : PoseLeaf))
    rw [List.map_map]
    apply List.map_congr_left
    intro r _
    change (dictionary.rows r).normalized (dictionary.denominators r) =
      (dictionary.rows r).normalized (dictionary.denominators r - 1 + 1)
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (positive r))]

theorem Bank.ofDictionary_pose {rowCount poseCount angleCount : Nat}
    (dictionary : Dictionary rowCount poseCount angleCount)
    (positive : ∀ r, 0 < dictionary.denominators r) (i : Fin poseCount) :
    (Bank.ofDictionary dictionary positive).poses i = dictionary.pose i := rfl

#print axioms Bank.ofDictionary
end N12Compact.DirectRecipeTable

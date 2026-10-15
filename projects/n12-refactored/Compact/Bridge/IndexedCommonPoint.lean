import Compact.Bridge.IndexedRawPairPlans
import Compact.Core.CommonPoint

/-! Four own-face checks give one point of an original square. The existing
pose realization supplies uniform inner-reference containment, and certified
input membership supplies every support bound. No center, orientation, or
foreign-owner premise is added by this bridge. -/

set_option Elab.async false

namespace N12Compact.IndexedCommonPoint
open S12 S12Pilot IntegerSupport IndexedRelaxation IndexedRawPairPlans

variable {r m a : Nat} {d : Dictionary r m a}

theorem point_sound (context : PoseContext d)
    (positive : ∀ i, 0 < d.denominators i)
    (keys : Fin 4 → Nat) (point : CommonPoint.Point)
    (checked : CommonPoint.check context.numeric keys point = true)
    (q : OpenSquare) (realizes : (d.pose context.pose).Realizes q)
    (block : ∀ i ∈ context.block, (d.rows i).Holds ![centerX q, centerY q]) :
    q.Inside point.value.1 point.value.2 := by
  have reference : context.numeric.reference = context.context.reference := by
    rw [context.numeric_exact]
    rfl
  have reference_checked : context.numeric.reference.value.Check := by
    rw [reference, context.reference_exact]
    exact (d.pose context.pose).angle.val.reference_checked
      (d.pose context.pose).angle.property 1 (by norm_num)
  have inputs : ∀ i ∈ d.poseRows context.pose,
      (d.rows i).Holds ![centerX q, centerY q] :=
    PairPruning.inputs_hold d.rows d.denominators positive (d.poseRows context.pose) _ realizes.1
  have inside := CommonPoint.inside_sound context.numeric keys point
    (fun p => ∀ i ∈ context.context.inputs, (d.rows i).Holds p)
    (context.context.cached_numeric_valid context.numeric context.numeric_exact)
    (by rw [reference]; exact context.reference_valid) reference_checked checked
    ![centerX q, centerY q]
    (by rw [context.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (block i) (inputs i))
  apply realizes.2 point.value
  simpa only [reference, context.reference_exact,
    Matrix.cons_val_zero, Matrix.cons_val_one] using inside

/-- A whole Cartesian family may reuse the same point; each square is checked
individually and no relative-axis comparison between the squares is required. -/
theorem pair_sound (x y : PoseContext d)
    (positive : ∀ i, 0 < d.denominators i)
    (xkeys ykeys : Fin 4 → Nat) (point : CommonPoint.Point)
    (xchecked : CommonPoint.check x.numeric xkeys point = true)
    (ychecked : CommonPoint.check y.numeric ykeys point = true)
    (q t : OpenSquare) (hq : (d.pose x.pose).Realizes q) (ht : (d.pose y.pose).Realizes t)
    (xblock : ∀ i ∈ x.block, (d.rows i).Holds ![centerX q, centerY q])
    (yblock : ∀ i ∈ y.block, (d.rows i).Holds ![centerX t, centerY t]) :
    ∃ u v, q.Inside u v ∧ t.Inside u v :=
  ⟨point.value.1, point.value.2,
    point_sound x positive xkeys point xchecked q hq xblock,
    point_sound y positive ykeys point ychecked t ht yblock⟩

end N12Compact.IndexedCommonPoint

#print axioms N12Compact.IndexedCommonPoint.point_sound
#print axioms N12Compact.IndexedCommonPoint.pair_sound

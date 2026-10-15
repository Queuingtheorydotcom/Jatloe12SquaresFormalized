import Compact.Cases.C898.CachedPairFan
import Compact.Core.CommonPoint

/-! Original-pose bridge for a checked common point. The integer point check
uses only four reference faces; the certified input rows and the actual inner
reference containment supply the original open-square conclusion. -/

set_option Elab.async false

namespace N12Compact.C898Cached
open S12 S12Pilot IntegerSupport PairPruning C898Shared

theorem PoseContext.point_sound (context : PoseContext)
    (raw : RawSupportFan.Context) (exact_raw : raw = context.context.numeric)
    (keys : Fin 4 → Nat) (point : CommonPoint.Point)
    (checked : CommonPoint.check raw keys point = true)
    (q : OpenSquare) (hq : (poses context.pose).Realizes q)
    (block : ∀ i ∈ context.block, (rows i).Holds ![centerX q, centerY q]) :
    q.Inside point.value.1 point.value.2 := by
  have ref_equal : raw.reference = references (poseAngle context.pose) := by
    rw [exact_raw]
    exact context.reference_exact
  have ref_value : raw.reference.value = (poses context.pose).angle.val.reference 1 := by
    rw [ref_equal]
    exact references_exact _
  have ref_valid : raw.reference.Valid := by
    rw [ref_equal]
    exact references_valid _
  have ref_checked : raw.reference.value.Check := by
    rw [ref_value]
    exact (poses context.pose).angle.val.reference_checked
      (poses context.pose).angle.property 1 (by norm_num)
  have inputs : ∀ i ∈ poseRows context.pose, (rows i).Holds ![centerX q, centerY q] :=
    inputs_hold rows denominators positive_denominators (poseRows context.pose) _ hq.1
  have inside := CommonPoint.inside_sound raw keys point
    (fun p => ∀ i ∈ context.context.inputs, (rows i).Holds p)
    (context.context.cached_numeric_valid raw exact_raw) ref_valid ref_checked checked
    ![centerX q, centerY q]
    (by rw [context.inputs_exact]
        intro i member
        exact (List.mem_append.mp member).elim (block i) (inputs i))
  apply hq.2 point.value
  simpa only [ref_value, Matrix.cons_val_zero, Matrix.cons_val_one] using inside

#print axioms PoseContext.point_sound

end N12Compact.C898Cached

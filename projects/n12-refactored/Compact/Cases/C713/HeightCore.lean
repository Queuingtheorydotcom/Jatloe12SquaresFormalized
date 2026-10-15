import Compact.Bridge.VertexCutRelaxation
import Compact.Bridge.AngleSection
import Compact.Cases.C713.SharedDictionary

/-! Numerical records for the original C713 owner7 height transfer. The
geometric height comes from actual occupied row points; every record checks
its original angle, certified radius, exact affine cut and outgoing pose. -/

namespace N12Compact.C713Height
open S12 S12Pilot IntegerSupport AngleSection VertexCutRelaxation HistoricalData

structure Entry where
  spec : Spec poseCount
  radius : Radius

def Entry.Check (entry : Entry) : Prop :=
  entry.spec.Check C713Shared.dictionary ∧
  entry.radius.Check (C713Shared.poses entry.spec.source).angle.val ∧
  entry.spec.cut.x = 0 ∧ entry.spec.cut.strict = false ∧ 0 < entry.spec.cut.y ∧
  (entry.spec.cut.constant : ℚ) +
    (entry.spec.cut.y : ℚ) * (87/50 + entry.radius.radius) = 0

noncomputable instance (entry : Entry) : Decidable entry.Check :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Name the target metadata separately so generated numeric checks use only
the actual target row list, never an inferred enumeration of all row IDs. -/
def Entry.TargetCheck (entry : Entry) : Prop :=
  match entry.spec.target with
  | none => True
  | some target =>
      C713Shared.dictionary.poseAngle entry.spec.source =
        C713Shared.dictionary.poseAngle target ∧
      ∀ i ∈ C713Shared.dictionary.poseRows target,
        (DirectPoseCover.Form.mk (C713Shared.dictionary.rows i) 0).StrictOK

noncomputable instance (entry : Entry) : Decidable entry.TargetCheck := by
  unfold Entry.TargetCheck
  cases entry.spec.target with
  | none => infer_instance
  | some target =>
      letI : Decidable (∀ i ∈ C713Shared.dictionary.poseRows target,
          (DirectPoseCover.Form.mk (C713Shared.dictionary.rows i) 0).StrictOK) :=
        List.decidableBAll _ (C713Shared.dictionary.poseRows target)
      infer_instance

theorem Entry.cut_holds (entry : Entry) (checked : entry.Check) (q : OpenSquare)
    (height : (87/50 : ℝ) + (entry.radius.radius : ℝ) < centerY q) :
    entry.spec.cut.Holds ![centerX q,centerY q] := by
  obtain ⟨_,_,hx,strict,hy,identity⟩ := checked
  have hy' : (0 : ℝ) < entry.spec.cut.y := by exact_mod_cast hy
  have identity' : (entry.spec.cut.constant : ℝ) +
      (entry.spec.cut.y : ℝ) * ((87/50 : ℝ) + (entry.radius.radius : ℝ)) = 0 := by
    have cast := congrArg (fun z : ℚ => (z : ℝ)) identity
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_intCast, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_zero] using cast
  have positive := mul_pos hy' (sub_pos.mpr height)
  simp only [Row.Holds,strict,Bool.false_eq_true,↓reduceIte,Row.eval,hx,
    Int.cast_zero,zero_mul,zero_add,Matrix.cons_val_one,Matrix.cons_val_zero]
  nlinarith only [positive,identity']

#print axioms Entry.cut_holds
end N12Compact.C713Height

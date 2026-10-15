import Compact.Bridge.IndexedRelaxation
import Compact.Bridge.DirectPoseCover
import Compact.Core.PlanarVertexSparse
import S12.SquareSupportBase

/-! Exact direct relaxation after a proved affine cut.
The complete original source pose, the actual container and the additional
cut imply either one original target pose or an empty domain. All boundary
intersections are checked; the geometric cut itself is supplied separately.
-/

set_option Elab.async false

namespace N12Compact.VertexCutRelaxation
open S12 S12Pilot IntegerSupport IndexedRelaxation DirectPoseCover PlanarVertex

variable {r m a : Nat}

def containerRows : List Row :=
  [⟨1,0,0,false⟩,⟨-1,0,4,false⟩,⟨0,1,0,false⟩,⟨0,-1,4,false⟩]

theorem containerRows_box : BoxNormals containerRows := by
  unfold BoxNormals
  decide

theorem containerRows_hold (q : OpenSquare) (box : InsideContainer q) :
    ∀ row ∈ containerRows, 0 ≤ row.eval ![centerX q, centerY q] := by
  obtain ⟨hx0,hx4,hy0,hy4⟩ := box _ _ (square_center_inside q)
  intro row member
  simp only [containerRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    norm_num [Row.eval] <;> linarith

structure Spec (m : Nat) where
  source : Fin m
  cut : Row
  target : Option (Fin m)

def Spec.base (w : Spec m) (d : Dictionary r m a) : List Row :=
  (w.cut :: (d.poseRows w.source).map d.rows) ++ containerRows

def Spec.targets (w : Spec m) (d : Dictionary r m a) : List Row :=
  match w.target with
  | none => [⟨0,0,-1,false⟩]
  | some target => (d.poseRows target).map d.rows

def Spec.Check (w : Spec m) (d : Dictionary r m a) : Prop :=
  PlanarVertexSparse.UnorderedCheck (w.base d) [] (w.targets d) ∧
  match w.target with
  | none => True
  | some target =>
      d.poseAngle w.source = d.poseAngle target ∧
      ∀ i ∈ d.poseRows target, (Form.mk (d.rows i) 0).StrictOK

instance (w : Spec m) (d : Dictionary r m a) : Decidable (w.Check d) := by
  unfold Spec.Check
  cases w.target with
  | none => infer_instance
  | some target =>
      letI : Decidable (∀ i ∈ d.poseRows target, (Form.mk (d.rows i) 0).StrictOK) :=
        List.decidableBAll _ (d.poseRows target)
      infer_instance

/-- A closed vertex computation preserves the original square and orientation.
No source row, open boundary, or possible source pose is discarded. -/
theorem Spec.sound (w : Spec m) (d : Dictionary r m a)
    (positive : ∀ i, 0 < d.denominators i) (checked : w.Check d)
    (q : OpenSquare) (incoming : (d.pose w.source).OrientedRealizes q)
    (box : InsideContainer q) (cut : w.cut.Holds ![centerX q,centerY q]) :
    OrientedPoseCovered (w.target.toList.map d.pose) q := by
  let p : Point := ![centerX q,centerY q]
  have source : ∀ i ∈ d.poseRows w.source, (d.rows i).Holds p := by
    intro i hi
    apply ((d.rows i).normalized_holds_iff _ (positive i) p).mp
    exact incoming.1.1 _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  have bounds : BoxNormals (w.base d) := containerRows_box.mono (by
    intro row member
    exact List.mem_append_right _ member)
  have feasible : PlanarVertex.Feasible (w.base d) [] p := by
    refine ⟨?_, by simp⟩
    intro row member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_cons.mp member with h | member
      · subst row
        exact w.cut.nonneg p cut
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
        exact (d.rows i).nonneg p (source i hi)
    · exact containerRows_hold q box row member
  have values := checked.1.toCheck.sound bounds p feasible
  cases target_eq : w.target with
  | none =>
      have impossible := values ⟨0,0,-1,false⟩ (by simp [Spec.targets,target_eq])
      norm_num [Row.eval] at impossible
  | some target =>
      have info : d.poseAngle w.source = d.poseAngle target ∧
          ∀ i ∈ d.poseRows target, (Form.mk (d.rows i) 0).StrictOK := by
        simpa only [target_eq] using checked.2
      refine ⟨d.pose target, by simp [target_eq], ?_⟩
      apply d.transfer info.1 positive q incoming
      intro i member
      have hnonneg : 0 ≤ (d.rows i).eval p := values (d.rows i) (by
        simp only [Spec.targets,target_eq]
        exact List.mem_map.mpr ⟨i,member,rfl⟩)
      exact ((Form.mk (d.rows i) 0).holds_iff p).mp
        ((Form.mk (d.rows i) 0).holds_of_nonnegative (info.2 i member) p hnonneg)

#print axioms Spec.sound
end N12Compact.VertexCutRelaxation

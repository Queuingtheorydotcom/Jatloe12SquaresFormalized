import S12.PoseBounds
import S12.AffineOverlap
import S12.RegionTree

namespace S12
open S12Pilot
set_option maxHeartbeats 0

def outerReference (w : AngleEnclosure) : ReferenceSquare := ⟨w.c,w.s,(1001/1000)*w.outer⟩
def pointForms (r : ReferenceSquare) (P : ℚ × ℚ) : RegionConstraints :=
  insideAffineForms r (Affine.coord 2 0) (Affine.coord 2 1) (Affine.const 2 P.1) (Affine.const 2 P.2)

def wallForms (w : AngleEnclosure) : RegionConstraints :=
  let a := Affine.const 2 (w.wall/2)
  let b := Affine.const 2 (4-w.wall/2)
  [⟨(Affine.coord 2 0).sub a,false⟩,⟨b.sub (Affine.coord 2 0),false⟩,
   ⟨(Affine.coord 2 1).sub a,false⟩,⟨b.sub (Affine.coord 2 1),false⟩]

def poseInputs (w : AngleEnclosure) (inside : List (ℚ × ℚ)) : RegionConstraints :=
  inside.flatMap (pointForms (outerReference w))++wallForms w++[⟨Affine.const 2 1,true⟩]
def poseForbidden (w : AngleEnclosure) (outside : List (ℚ × ℚ)) : List RegionConstraints :=
  outside.map (pointForms (w.reference 1))

theorem poseInputs_sound (w : AngleEnclosure) (hw : w.Check) (inside : List (ℚ × ℚ))
    (q : OpenSquare) (t : ℝ) (hc : q.c=normalC t) (hs : q.s=normalS t)
    (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ))
    (ha : 1<q.side) (hsize : q.side≤1001/1000) (hbox : InsideContainer q)
    (hi : ∀ P∈inside,q.Inside P.1 P.2) :
    ∀ f∈poseInputs w inside,f.Holds ![centerX q,centerY q] := by
  intro f hf
  simp only [poseInputs,List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · obtain ⟨P,hP,hf⟩ := List.mem_flatMap.mp hf
    have hh := w.outer_sound hw (1001/1000) q t P.1 P.2 hc hs ht0 ht1 (by norm_num; exact hsize) (hi P hP)
    apply ((insideAffineForms_iff (outerReference w) _ _ _ _ _).mpr ?_) f hf
    simpa [outerReference,Affine.eval_coord,Affine.eval_const] using hh
  · have hh := w.wall_sound hw 1 (by norm_num) q t hc hs ht0 ht1 (by norm_num; exact ha.le) hbox
    simp only [wallForms,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp only [LinearConstraint.Holds,if_false,Affine.eval_sub,Affine.eval_const,Affine.eval_coord,
        Matrix.cons_val_zero,Matrix.cons_val_one] <;> push_cast <;> norm_num at hh ⊢ <;>
      linarith [hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
  · have he : f=⟨Affine.const 2 1,true⟩ := List.mem_singleton.mp hf
    rw [he]
    simp [LinearConstraint.Holds]

theorem poseForbidden_sound (w : AngleEnclosure) (hw : w.Check) (outside : List (ℚ × ℚ))
    (q : OpenSquare) (t : ℝ) (hc : q.c=normalC t) (hs : q.s=normalS t)
    (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ)) (ha : 1<q.side)
    (ho : ∀ P∈outside,¬q.Inside P.1 P.2) :
    ∀ block∈poseForbidden w outside,¬(∀ f∈block,f.Holds ![centerX q,centerY q]) := by
  intro block hb hblock
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hb
  have hr := w.reference_checked hw 1 (by norm_num)
  have hh := insideAffineForms_sound (w.reference 1) hr (Affine.coord 2 0) (Affine.coord 2 1)
    (Affine.const 2 P.1) (Affine.const 2 P.2) ![centerX q,centerY q] hblock
  simp only [Affine.eval_const,Affine.eval_coord,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  have hinner := w.inner_sound hw 1 (by norm_num) q t hc hs ht0 ht1 (by norm_num; exact ha.le) (ratPoint P)
  exact ho P hP (hinner hh)

structure PoseRoot where
  angle : {w : AngleEnclosure // w.Check}
  tree : RegionTree

def PoseRoot.Check (r : PoseRoot) (inside outside : List (ℚ × ℚ)) : Prop :=
  r.tree.Check (poseInputs r.angle.val inside) (poseForbidden r.angle.val outside)
instance PoseRoot.decidableCheck (r : PoseRoot) (inside outside : List (ℚ × ℚ)) : Decidable (r.Check inside outside) :=
  inferInstanceAs (Decidable (RegionTree.Check _ _ _))

/-- The complete geometric meaning of a checked center-region tree. -/
theorem PoseRoot.sound (r : PoseRoot) (inside outside : List (ℚ × ℚ)) (hr : r.Check inside outside)
    (q : OpenSquare) (t : ℝ) (hc : q.c=normalC t) (hs : q.s=normalS t)
    (ht0 : (r.angle.val.lower:ℝ)≤t) (ht1 : t≤(r.angle.val.upper:ℝ))
    (ha : 1<q.side) (hsize : q.side≤1001/1000) (hbox : InsideContainer q)
    (hi : ∀ P∈inside,q.Inside P.1 P.2) (ho : ∀ P∈outside,¬q.Inside P.1 P.2) :
    ∃ leaf∈r.tree.leaves (poseInputs r.angle.val inside),
      ∀ f∈leaf,f.Holds ![centerX q,centerY q] :=
  r.tree.sound _ _ hr _ (poseInputs_sound r.angle.val r.angle.property inside q t hc hs ht0 ht1 ha hsize hbox hi)
    (poseForbidden_sound r.angle.val r.angle.property outside q t hc hs ht0 ht1 ha ho)

#print axioms PoseRoot.sound
end S12

import S12.PoseRegion
import S12.IntervalCoverage

namespace S12
open S12Pilot

structure PoseLeaf where
  angle : {w : AngleEnclosure // w.Check}
  inputs : RegionConstraints

def PoseLeaf.Realizes (leaf : PoseLeaf) (q : OpenSquare) : Prop :=
  (∀ f∈leaf.inputs,f.Holds ![centerX q,centerY q]) ∧
  (∀ P : ℝ × ℝ,P-(centerX q,centerY q)∈squareSet
    ((leaf.angle.val.reference 1).toSquare (leaf.angle.val.reference_checked leaf.angle.property 1 (by norm_num))) →
    P∈squareSet q)

def PoseRoot.leaves (r : PoseRoot) (inside : List (ℚ × ℚ)) : List PoseLeaf :=
  (r.tree.leaves (poseInputs r.angle.val inside)).map (fun inputs => ⟨r.angle,inputs⟩)

structure OwnerEnclosure where
  inside : List (ℚ × ℚ)
  outside : List (ℚ × ℚ)
  roots : List {r : PoseRoot // r.Check inside outside}

def OwnerEnclosure.Check (w : OwnerEnclosure) : Prop :=
  CoversInterval 0 1 (w.roots.map (fun r => r.val.angle.val))
instance OwnerEnclosure.decidableCheck (w : OwnerEnclosure) : Decidable w.Check :=
  inferInstanceAs (Decidable (CoversInterval _ _ _))

def OwnerEnclosure.leaves (w : OwnerEnclosure) : List PoseLeaf :=
  w.roots.flatMap (fun r => r.val.leaves w.inside)

/-- Real ownership, wall containment and side bounds imply membership in
one of the checked leaves, with its inner reference containment proved. -/
theorem OwnerEnclosure.sound (w : OwnerEnclosure) (hw : w.Check) (q : OpenSquare)
    (ha : 1<q.side) (hsize : q.side≤1001/1000) (hbox : InsideContainer q)
    (hi : ∀ P∈w.inside,q.Inside P.1 P.2) (ho : ∀ P∈w.outside,¬q.Inside P.1 P.2) :
    ∃ leaf∈w.leaves,leaf.Realizes q := by
  obtain ⟨r,hc,hs,hside,hX,hY,hinside⟩ := exists_positive_frame q
  obtain ⟨t,ht0,ht1,hs',hc'⟩ := first_quadrant_rational r.s r.c hs hc (by nlinarith [r.unit_normal])
  obtain ⟨angle,hangle,htlo,hthi⟩ := coversInterval_sound _ 0 1 hw t (by simpa using ht0) (by simpa using ht1)
  obtain ⟨root,hroot,he⟩ := List.mem_map.mp hangle
  subst angle
  have hi' : ∀ P∈w.inside,r.Inside P.1 P.2 := fun P hP => (hinside _ _).mpr (hi P hP)
  have ho' : ∀ P∈w.outside,¬r.Inside P.1 P.2 := fun P hP hh => ho P hP ((hinside _ _).mp hh)
  have hbox' : InsideContainer r := fun x y hh => hbox x y ((hinside x y).mp hh)
  obtain ⟨inputs,hinputs,hholds⟩ := root.val.sound w.inside w.outside root.property r t hc' hs' htlo hthi
    (by rw [hside]; exact ha) (by rw [hside]; exact hsize) hbox' hi' ho'
  refine ⟨⟨root.val.angle,inputs⟩,?_,?_,?_⟩
  · exact List.mem_flatMap.mpr ⟨root,hroot,List.mem_map.mpr ⟨inputs,hinputs,rfl⟩⟩
  · simpa only [hX,hY] using hholds
  · intro P hP
    apply (hinside P.1 P.2).mp
    apply root.val.angle.val.inner_sound root.val.angle.property 1 (by norm_num) r t hc' hs' htlo hthi
      (by norm_num; rw [hside]; exact ha.le) P
    simpa only [hX,hY] using hP

structure OwnerPairCertificate where
  first : {w : OwnerEnclosure // w.Check}
  second : {w : OwnerEnclosure // w.Check}
  overlaps : List {w : AffineOverlapCertificate // w.Check}

def OwnerPairCertificate.Check (w : OwnerPairCertificate) : Prop :=
  ∀ a∈w.first.val.leaves,∀ b∈w.second.val.leaves,∃ c∈w.overlaps,
    c.val.first.val=a.angle.val.reference 1 ∧ c.val.second.val=b.angle.val.reference 1 ∧
    c.val.inputsA=a.inputs ∧ c.val.inputsB=b.inputs
instance OwnerPairCertificate.decidableCheck (w : OwnerPairCertificate) : Decidable w.Check :=
  inferInstanceAs (Decidable (∀ a∈w.first.val.leaves,_))

/-- Complete pair exclusion: angle coverage, center-tree coverage, reference
containment, every leaf pair, and every linear witness are checked. -/
theorem OwnerPairCertificate.sound (w : OwnerPairCertificate) (hw : w.Check) (q r : OpenSquare)
    (ha : 1<q.side) (hb : 1<r.side) (hsa : q.side≤1001/1000) (hsb : r.side≤1001/1000)
    (hqa : InsideContainer q) (hqb : InsideContainer r)
    (hAi : ∀ P∈w.first.val.inside,q.Inside P.1 P.2)
    (hAo : ∀ P∈w.first.val.outside,¬q.Inside P.1 P.2)
    (hBi : ∀ P∈w.second.val.inside,r.Inside P.1 P.2)
    (hBo : ∀ P∈w.second.val.outside,¬r.Inside P.1 P.2)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : False := by
  obtain ⟨a,hLa,hAa,hAr⟩ := w.first.val.sound w.first.property q ha hsa hqa hAi hAo
  obtain ⟨b,hLb,hBa,hBr⟩ := w.second.val.sound w.second.property r hb hsb hqb hBi hBo
  obtain ⟨c,_,hca,hcb,hia,hib⟩ := hw a hLa b hLb
  have hh := c.val.sound c.property ![centerX q,centerY q,centerX r,centerY r]
    (by simpa only [hia,Matrix.cons_val_zero,Matrix.cons_val_one] using hAa)
    (by simpa only [hib,Matrix.cons_val_two,Matrix.cons_val_three] using hBa)
  obtain ⟨P,hPq,hPr⟩ := hh
  have hqa' : P∈squareSet q := hAr P (by simpa only [hca,Matrix.cons_val_zero,Matrix.cons_val_one] using hPq)
  have hqb' : P∈squareSet r := hBr P (by simpa only [hcb,Matrix.cons_val_two,Matrix.cons_val_three] using hPr)
  exact hd P.1 P.2 ⟨hqa',hqb'⟩

#print axioms OwnerPairCertificate.sound
end S12

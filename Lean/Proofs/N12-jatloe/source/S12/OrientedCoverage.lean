import S12.ContinuousCertificate
namespace S12
open S12Pilot
set_option maxHeartbeats 0

/-- The actual square has a face indexing whose real half-angle lies in this
leaf's interval. This is stronger than containing the inner reference square. -/
def PoseLeaf.AngleWitness (leaf : PoseLeaf) (q : OpenSquare) : Prop :=
  ∃ r : OpenSquare,∃ t : ℝ,
    r.c=normalC t ∧ r.s=normalS t ∧
    (leaf.angle.val.lower:ℝ)≤t ∧ t≤(leaf.angle.val.upper:ℝ) ∧
    r.side=q.side ∧ centerX r=centerX q ∧ centerY r=centerY q ∧
    ∀ x y,r.Inside x y ↔ q.Inside x y

def PoseLeaf.OrientedRealizes (leaf : PoseLeaf) (q : OpenSquare) : Prop :=
  leaf.Realizes q ∧ leaf.AngleWitness q
def OrientedPoseCovered (leaves : List PoseLeaf) (q : OpenSquare) : Prop :=
  ∃ leaf∈leaves,leaf.OrientedRealizes q

theorem oriented_coverage_forget (leaves : List PoseLeaf) (q : OpenSquare)
    (h : OrientedPoseCovered leaves q) : PoseCovered leaves q := by
  obtain ⟨leaf,hl,hh⟩ := h
  exact ⟨leaf,hl,hh.1⟩

/-- The initial enclosure retains the actual orientation witness as well as
the reference-square and center information. -/
theorem OwnerEnclosure.oriented_sound (w : OwnerEnclosure) (hw : w.Check) (q : OpenSquare)
    (ha : 1<q.side) (hsize : q.side≤1001/1000) (hbox : InsideContainer q)
    (hi : ∀ P∈w.inside,q.Inside P.1 P.2) (ho : ∀ P∈w.outside,¬q.Inside P.1 P.2) :
    OrientedPoseCovered w.leaves q := by
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
  refine ⟨⟨root.val.angle,inputs⟩,?_,⟨?_,?_⟩,?_⟩
  · exact List.mem_flatMap.mpr ⟨root,hroot,List.mem_map.mpr ⟨inputs,hinputs,rfl⟩⟩
  · simpa only [hX,hY] using hholds
  · intro P hP
    apply (hinside P.1 P.2).mp
    apply root.val.angle.val.inner_sound root.val.angle.property 1 (by norm_num) r t hc' hs' htlo hthi
      (by norm_num; rw [hside]; exact ha.le) P
    simpa only [hX,hY] using hP
  · exact ⟨r,t,hc',hs',htlo,hthi,hside,hX,hY,hinside⟩

def RelaxationLink.AngleCheck (w : RelaxationLink) : Prop :=
  w.target.angle.val.lower≤w.source.angle.val.lower ∧
  w.source.angle.val.upper≤w.target.angle.val.upper
instance RelaxationLink.decidableAngleCheck (w : RelaxationLink) : Decidable w.AngleCheck :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem RelaxationLink.oriented_sound (w : RelaxationLink) (hw : w.Check) (hang : w.AngleCheck)
    (q : OpenSquare) (h : w.source.OrientedRealizes q) : w.target.OrientedRealizes q := by
  refine ⟨w.sound hw q h.1,?_⟩
  obtain ⟨r,t,hc,hs,hlo,hhi,hside,hX,hY,hin⟩ := h.2
  have hl : (w.target.angle.val.lower:ℝ)≤(w.source.angle.val.lower:ℝ) := by exact_mod_cast hang.1
  have hu : (w.source.angle.val.upper:ℝ)≤(w.target.angle.val.upper:ℝ) := by exact_mod_cast hang.2
  exact ⟨r,t,hc,hs,le_trans hl hlo,le_trans hhi hu,hside,hX,hY,hin⟩

theorem oriented_relaxation_cover_sound (sources targets : List PoseLeaf)
    (links : List {w : RelaxationLink // w.Check})
    (hw : RelaxationCoverCheck sources targets links)
    (hang : ∀ w∈links,w.val.AngleCheck) (q : OpenSquare)
    (h : OrientedPoseCovered sources q) : OrientedPoseCovered targets q := by
  obtain ⟨s,hs,hq⟩ := h
  obtain ⟨w,hm,he,ht⟩ := hw s hs
  exact ⟨w.val.target,ht,w.val.oriented_sound w.property (hang w hm) q (by simpa only [he] using hq)⟩

theorem PosePruning.oriented_sound {source : PoseLeaf} {neighbors : List PoseLeaf}
    (w : PosePruning source neighbors) (q r : OpenSquare) (hq : source.OrientedRealizes q)
    (hr : PoseCovered neighbors r) (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    OrientedPoseCovered w.result q := by
  obtain ⟨leaf,hl,hh⟩ := w.sound q r hq.1 hr hd
  have he : leaf.angle=source.angle := by
    obtain ⟨inputs,_,rfl⟩ := List.mem_map.mp hl
    rfl
  exact ⟨leaf,hl,hh,by simpa only [PoseLeaf.AngleWitness,he] using hq.2⟩

theorem CertifiedPosePruning.oriented_sound (w : CertifiedPosePruning)
    (hang : ∀ l∈w.links,l.val.AngleCheck) (q r : OpenSquare)
    (hq : w.source.OrientedRealizes q) (hr : PoseCovered w.neighbors r)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : OrientedPoseCovered w.targets q :=
  oriented_relaxation_cover_sound _ _ w.links w.covered hang q (w.pruning.oriented_sound q r hq hr hd)

theorem oriented_pruning_cover_sound (sources neighbors targets : List PoseLeaf)
    (plans : List CertifiedPosePruning) (hw : PruningCoverCheck sources neighbors targets plans)
    (hang : ∀ w∈plans,∀ l∈w.links,l.val.AngleCheck) (q r : OpenSquare)
    (hq : OrientedPoseCovered sources q) (hr : PoseCovered neighbors r)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : OrientedPoseCovered targets q := by
  obtain ⟨s,hs,hq⟩ := hq
  obtain ⟨w,hm,he,hn,ht⟩ := hw s hs
  obtain ⟨t,hm',hq⟩ := w.oriented_sound (hang w hm) q r
    (by simpa only [he] using hq) (by simpa only [hn] using hr) hd
  exact ⟨t,ht t hm',hq⟩

#print axioms OwnerEnclosure.oriented_sound
#print axioms oriented_pruning_cover_sound
end S12

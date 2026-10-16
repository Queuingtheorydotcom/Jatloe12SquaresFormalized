import Compact.Cases.C868.ActualCrosspoints
import Compact.Cases.C868.NegativeCornerSector
import Compact.Geometry.MergedLeftNegative
import Compact.Completion.CommonCases.SingletonMissing

/-! The nonnegative upper-central sector has an actual strict centre.
The antidiagonal reflection transports the entire top-wall square and
each genuine foreign point; it does not exchange the two lower central
owners.  The surviving sector below remains a reduction, not an exclusion. -/
namespace N12Compact.C868
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private def antidiagonal (q : OpenSquare) : OpenSquare :=
  pullSwap (pullX (pullY q))

private theorem inside_antidiagonal (q : OpenSquare) (x y : ℝ) :
    (antidiagonal q).Inside x y ↔ q.Inside (4-y) (4-x) := by
  simp only [antidiagonal,inside_pullSwap,inside_pullX,inside_pullY]

/-- The actual top owner supplies its leftward F3 reach.  The missing
upper/lower row points belong to C16/T32768, and the additional corner
point belongs to the genuine W4096. -/
theorem upper_nonnegative_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (H : OpenSquare)
    (hc : 0<H.c) (hs : 0≤H.s) (canonical : H.s≤H.c)
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    H.Inside 2 2 := by
  let A := turnFrame (antidiagonal H)
  let L := antidiagonal (owner p 32768)
  have ai (x y : ℝ) : A.Inside x y↔H.Inside (4-y) (4-x) := by
    simp only [A,turnFrame_inside,inside_antidiagonal]
  have ac : A.c=H.c := by dsimp only [A,antidiagonal,turnFrame,pullSwap,pullX,pullY]; ring
  have asine : A.s= -H.s := rfl
  have size : 1<A.side := by
    change 1<H.side
    rw [shape,show (owner p 3072).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  have same : A.side=L.side := by
    change H.side=(owner p 32768).side
    rw [shape,show (owner p 3072).side=p.commonSide from p.congruent _,
      show (owner p 32768).side=p.commonSide from p.congruent _]
  have box : InsideContainer L :=
    container_pullSwap _ (container_pullX _ (container_pullY _ (p.contained _)))
  have missing (mask : Nat) (hm : mask∈family) (hne : 3072≠mask)
      (x y : ℝ) (point : (owner p mask).Inside x y) : ¬H.Inside x y :=
    fun own => apart p hf 3072 mask (by decide +kernel) hm hne x y
      ⟨(inside x y).mp own,point⟩
  have centre := MergedLeftNegative.point A L size same box
    (by simpa only [ac] using hc)
    (by rw [asine]; linarith only [hs])
    (by rw [asine,ac]; linarith only [canonical])
    (by
      apply (ai _ _).mpr
      norm_num only
      apply (inside _ _).mpr
      simpa using seed_inside p hf 3072 (by decide +kernel)
        (47/20,47/20) (by decide +kernel))
    (by
      apply (ai _ _).mpr
      norm_num only
      apply (inside _ _).mpr
      simpa using seed_inside p hf 3072 (by decide +kernel)
        (33/20,47/20) (by decide +kernel))
    (by
      intro own
      have actual := (ai _ _).mp own
      norm_num only at actual
      exact missing 16 (by decide +kernel) (by decide +kernel) _ _
        (by simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 1)
        actual)
    (by
      intro own
      have actual := (ai _ _).mp own
      norm_num only at actual
      exact missing 32768 (by decide +kernel) (by decide +kernel) _ _
        (by simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 2)
        actual)
    (by
      intro own
      have actual := (ai _ _).mp own
      norm_num only at actual
      exact missing 4096 (by decide +kernel) (by decide +kernel) _ _
        (by simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 3)
        actual)
    (by
      apply (inside_antidiagonal _ _ _).mpr
      norm_num only
      simpa using seed_inside p hf 32768 (by decide +kernel)
        (2,1543/500) (by decide +kernel))
    (by
      apply (inside_antidiagonal _ _ _).mpr
      norm_num only
      simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 6)
    (by
      intro x y own
      exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (4-y) (4-x)
        ⟨(inside _ _).mp ((ai x y).mp own.1),
          (inside_antidiagonal _ _ _).mp own.2⟩)
  have original := (ai 2 2).mp centre
  norm_num only at original
  exact original

/-- These are necessary conditions for the still-open second sector.
In particular the stronger singleton points belong to L2, while the
corner belongs to O1; neither is transferred to A256 or to the wall. -/
theorem nonnegative_upper_residue (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (A H : OpenSquare)
    (ac : 0<A.c) (aCanonical : |A.s|≤A.c)
    (hc : 0<H.c) (hs : 0≤H.s) (hCanonical : H.s≤H.c)
    (sa : A.side=(owner p 256).side) (sh : H.side=(owner p 3072).side)
    (ia : ∀ x y,A.Inside x y↔(owner p 256).Inside x y)
    (ih : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    A.s<0 ∧ (owner p 1).Inside 1 1 ∧ H.Inside 2 2 ∧
      A.loV+A.side≤2*(A.c-A.s) ∧
      (owner p 2).Inside 1 (91/50) ∧ (owner p 2).Inside (19/25) (49/25) := by
  have hNormal : C977CornerCubic.Normal H.c H.s := ⟨hs,hCanonical,H.unit_normal⟩
  have negative : A.s<0 := by
    apply lt_of_not_ge
    intro sign
    exact positive_frames_impossible p hf A H
      ⟨sign,by simpa only [abs_of_nonneg sign] using aCanonical,A.unit_normal⟩
      hNormal sa sh ia ih
  have aNormal : C977CornerCubic.Normal A.c (-A.s) :=
    ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using aCanonical,
      by nlinarith only [A.unit_normal]⟩
  have corner : (owner p 1).Inside 1 1 := by
    by_contra absent
    exact negative_corner_frames_impossible p hf A H aNormal hNormal sa sh ia ih absent
  have center := upper_nonnegative_center p hf H hc hs hCanonical sh ih
  have absent : ¬A.Inside 2 2 := fun own =>
    apart p hf 256 3072 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨(ia _ _).mp own,(ih _ _).mp center⟩
  have marker : A.Inside (33/20) (33/20) := (ia _ _).mpr (by
    simpa using seed_inside p hf 256 (by decide +kernel)
      (33/20,33/20) (by decide +kernel))
  have below := (ia _ _).mpr (southwest_crosspoints p hf).2
  have height : A.loV+A.side≤2*(A.c-A.s) := by
    apply le_of_not_gt
    intro high
    apply absent
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [marker.1,(abs_le.mp aCanonical).1]
    · linarith only [below.2.1,negative]
    · linarith only [marker.2.2.1,ac,negative]
    · linarith only [high]
  have leftMissing : ¬(owner p 2).Inside 1 1 := fun own =>
    apart p hf 1 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨corner,own⟩
  have code : markerCode p (ownerIndex p 2)=2 := ownerIndex_spec p 2
    (by rw [hf]; decide +kernel)
  have support : maskSupport 2=({1}:Finset Marker) := by decide +kernel
  have exactMarkers : ExactMarkers (owner p 2) {1} := by
    simpa only [owner,code,support] using coded_exact p (ownerIndex p 2)
  have stronger := CommonCases.SingletonMissing.one_missing_points (owner p 2)
    (by rw [show (owner p 2).side=p.commonSide from p.congruent _]; exact p.side_gt_one)
    (by rw [show (owner p 2).side=p.commonSide from p.congruent _]; exact p.side_le)
    (p.contained _) exactMarkers leftMissing
  exact ⟨negative,corner,center,height,stronger.1,stronger.2⟩

#print axioms upper_nonnegative_center
#print axioms nonnegative_upper_residue
end
end N12Compact.C868

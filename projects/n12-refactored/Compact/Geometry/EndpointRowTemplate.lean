import Compact.Geometry.FourSquareLowerBarrier
import Compact.Geometry.CentralCross

/-! The actual horizontal positions of a unit-height span force a point.
This replaces the anonymous unit-section argument when the two endpoints
are (1.74,2) and (1.6,3). Only the right wall is used to raise A; L is used
solely through its already owned point (1,2.4). -/
namespace N12Compact.EndpointRowTemplate

open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem canonical_left (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hsc : |q.s| ≤ q.c)
    (low : q.Inside (87/50) 2) (top : q.Inside (8/5) 3)
    (missingRow : ¬ q.Inside 2 (12/5))
    (missingHigh : ¬ q.Inside 2 (5/2)) : q.Inside 1 (12/5) := by
  obtain ⟨hslo,hshi⟩ := abs_le.mp hsc
  have hc1 : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s]
  have rowUlo : q.loU < q.c*2+q.s*(12/5) := by
    linarith only [low.1,top.1,hc]
  have rowVlo : q.loV < -q.s*2+q.c*(12/5) := by
    linarith only [low.2.2.1,hshi,hc]
  have rowVhi : -q.s*2+q.c*(12/5) < q.loV+q.side := by
    linarith only [top.2.2.2,hslo,hc]
  have rowFace : q.loU+q.side ≤ q.c*2+q.s*(12/5) :=
    le_of_not_gt (fun hu => missingRow ⟨rowUlo,hu,rowVlo,rowVhi⟩)
  have highUlo : q.loU < q.c*2+q.s*(5/2) := by
    linarith only [low.1,top.1,hc]
  have highVlo : q.loV < -q.s*2+q.c*(5/2) := by
    linarith only [low.2.2.1,hshi,hc]
  have highVhi : -q.s*2+q.c*(5/2) < q.loV+q.side := by
    linarith only [top.2.2.2,hslo,hc]
  have highFace : q.loU+q.side ≤ q.c*2+q.s*(5/2) :=
    le_of_not_gt (fun hu => missingHigh ⟨highUlo,hu,highVlo,highVhi⟩)
  have slope : 0 < (13/50)*q.c+(1/2)*q.s := by
    linarith only [low.2.1,highFace]
  simp only [OpenSquare.Inside,InBands,mul_one]
  exact ⟨by linarith only [rowFace,ha,hc1],
    by linarith only [top.2.1,hslo],
    by linarith only [low.2.2.1,slope,hc],
    by linarith only [top.2.2.2,hshi]⟩

/-- All orientations, with no side cap or container assumption. The two
missing points select actual faces; they are not a pose enclosure. -/
theorem forced_left (q : OpenSquare) (ha : 1 < q.side)
    (low : q.Inside (87/50) 2) (top : q.Inside (8/5) 3)
    (missingRow : ¬ q.Inside 2 (12/5))
    (missingHigh : ¬ q.Inside 2 (5/2)) : q.Inside 1 (12/5) := by
  obtain ⟨r,hc,hsc,hside,hi,_⟩ := ClosedFrames.canonical_frame q
  exact (hi _ _).mp (canonical_left r (by simpa only [hside] using ha) hc hsc
    ((hi _ _).mpr low) ((hi _ _).mpr top)
    (fun hp => missingRow ((hi _ _).mp hp))
    (fun hp => missingHigh ((hi _ _).mp hp)))

structure Premises (A B L R : OpenSquare) : Prop where
  aSide : 1 < A.side
  bSide : 1 < B.side
  rSide : 1 < R.side
  rBox : InsideContainer R
  aP : ClosedInside A 2 (113/50)
  aQ : ClosedInside A (113/50) 2
  aT : ClosedInside A (47/20) (47/20)
  aF : ¬ A.Inside (33/20) (33/20)
  aG : ¬ A.Inside (47/20) (33/20)
  bMarker : ClosedInside B (33/20) (47/20)
  bLow : B.Inside (87/50) 2
  bHigh : B.Inside (8/5) 3
  lQ : ClosedInside L 1 (12/5)
  rP : ClosedInside R (1543/500) 2
  rQ : ClosedInside R 3 (12/5)
  rMissingLow : ¬ R.Inside 3 (87/50)
  ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)
  ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)
  bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)

theorem impossible (A B L R : OpenSquare) (h : Premises A B L R) : False := by
  have highR : R.Inside 3 (5/2) := FourSquareLowerBarrier.right_point R A
    h.rSide h.rBox h.rP h.rQ h.rMissingLow h.aQ
    (fun x y hp => h.ar x y ⟨hp.2,hp.1⟩)
  have foreignB := ClosedPointExclusion.outside_of_closed A B _ _ h.ab h.bMarker
  have foreignR := ClosedPointExclusion.outside_of_closed A R _ _ h.ar h.rQ
  have foreignHigh : ¬ A.Inside 3 (5/2) := fun hp => h.ar _ _ ⟨hp,highR⟩
  obtain ⟨a,hc,hs,hside,hi,hcl⟩ := ClosedFrames.positive_frame A
  have highA : A.Inside 2 (5/2) := (hi _ _).mp
    (FourSquareANarrow.point_of_higher_R a (by simpa only [hside] using h.aSide) hc hs
      ((hcl _ _).mpr h.aP) ((hcl _ _).mpr h.aQ) ((hcl _ _).mpr h.aT)
      (fun hp => h.aF ((hi _ _).mp hp)) (fun hp => h.aG ((hi _ _).mp hp))
      (fun hp => foreignB ((hi _ _).mp hp)) (fun hp => foreignR ((hi _ _).mp hp))
      (fun hp => foreignHigh ((hi _ _).mp hp)))
  have rowA := FourSquareAForced.row_point A h.aP highA
  have leftB := forced_left B h.bSide h.bLow h.bHigh
    (fun hp => h.ab _ _ ⟨rowA,hp⟩) (fun hp => h.ab _ _ ⟨highA,hp⟩)
  exact ClosedPointExclusion.outside_of_closed B L _ _ h.bl h.lQ leftB

private theorem closed_swap (q : OpenSquare) (x y : ℝ) :
    ClosedInside (pullSwap q) x y ↔ ClosedInside q y x := by
  dsimp [ClosedInside,pullSwap]
  constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- The elbow triangle reaches one of its two arms. Both alternatives are
retained, so no right-wall high point is needed to choose an orientation. -/
theorem two_arms (q : OpenSquare) (ha : 1 < q.side)
    (hP : ClosedInside q 2 (113/50)) (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hF : ¬ q.Inside (33/20) (33/20)) (hG : ¬ q.Inside (47/20) (33/20))
    (hB : ¬ q.Inside (33/20) (47/20)) (hR : ¬ q.Inside 3 (12/5))
    (hTop : ¬ q.Inside (12/5) 3) :
    q.Inside 2 (5/2) ∨ q.Inside (5/2) 2 :=
  CentralCross.point q ha hP hQ hT hF hG hB hR hTop

structure DualPremises (A B C L D : OpenSquare) : Prop where
  aSide : 1 < A.side
  bSide : 1 < B.side
  cSide : 1 < C.side
  aP : ClosedInside A 2 (113/50)
  aQ : ClosedInside A (113/50) 2
  aT : ClosedInside A (47/20) (47/20)
  aF : ¬ A.Inside (33/20) (33/20)
  aG : ¬ A.Inside (47/20) (33/20)
  aB : ¬ A.Inside (33/20) (47/20)
  aR : ¬ A.Inside 3 (12/5)
  aTop : ¬ A.Inside (12/5) 3
  bLow : B.Inside (87/50) 2
  bHigh : B.Inside (8/5) 3
  cLow : C.Inside 2 (87/50)
  cHigh : C.Inside 3 (8/5)
  lQ : ClosedInside L 1 (12/5)
  dQ : ClosedInside D (12/5) 1
  ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)
  ac : ∀ x y, ¬ (A.Inside x y ∧ C.Inside x y)
  bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)
  cd : ∀ x y, ¬ (C.Inside x y ∧ D.Inside x y)

/-- Both arm alternatives end in actual overlap, using perpendicular spans.
No wall assumption, missing lower wall point, or side upper bound is used. -/
theorem dual_impossible (A B C L D : OpenSquare)
    (h : DualPremises A B C L D) : False := by
  rcases two_arms A h.aSide h.aP h.aQ h.aT h.aF h.aG h.aB h.aR h.aTop with up | right
  · have rowA := FourSquareAForced.row_point A h.aP up
    have leftB := forced_left B h.bSide h.bLow h.bHigh
      (fun hp => h.ab _ _ ⟨rowA,hp⟩) (fun hp => h.ab _ _ ⟨up,hp⟩)
    exact ClosedPointExclusion.outside_of_closed B L _ _ h.bl h.lQ leftB
  · have swappedRow := FourSquareAForced.row_point (pullSwap A)
      ((closed_swap A _ _).mpr h.aQ) ((inside_pullSwap A _ _).mpr right)
    have rowA := (inside_pullSwap A _ _).mp swappedRow
    have bottomC := forced_left (pullSwap C) (by simpa only [pullSwap] using h.cSide)
      ((inside_pullSwap C _ _).mpr h.cLow) ((inside_pullSwap C _ _).mpr h.cHigh)
      (fun hp => h.ac _ _ ⟨rowA,(inside_pullSwap C _ _).mp hp⟩)
      (fun hp => h.ac _ _ ⟨right,(inside_pullSwap C _ _).mp hp⟩)
    exact ClosedPointExclusion.outside_of_closed C D _ _ h.cd h.dQ
      ((inside_pullSwap C _ _).mp bottomC)

#print axioms forced_left
#print axioms impossible
#print axioms dual_impossible
end N12Compact.EndpointRowTemplate

import Compact.Geometry.ClosedFrames
import S12.ShortCluster
import S12.Convex

/-! A genuine neighboring wall segment excludes the middle-angle escape
of an elbow square from the container center. This is a continuous local
reduction, not a whole packing exclusion. No neighbor orientation, side
bound, or container premise is substituted for the two actual endpoints. -/
namespace N12Compact.CentralEscapeSegment
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

/-- In a positive shallow frame, the actual right-wall segment forces the
center whenever the elbow angle is at least `atan (16/25)`. -/
theorem shallow_center (A R : OpenSquare) (ha : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (steep : (16/25)*A.c ≤ A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (t : A.Inside (47/20) (47/20))
    (missingTop : ¬ A.Inside (12/5) 3)
    (rMarker : R.Inside (1543/500) 2) (rPoint : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 2 := by
  by_contra missing
  have centerUhi : A.c*2+A.s*2 < A.loU+A.side := by
    linarith only [t.2.1,hc,hs]
  have centerVlo : A.loV < -A.s*2+A.c*2 := by
    linarith only [q.2.2.1,hs]
  have centerVhi : -A.s*2+A.c*2 < A.loV+A.side := by
    linarith only [p.2.2.2,hc]
  have centerU : A.c*2+A.s*2 ≤ A.loU :=
    le_of_not_gt (fun h => missing ⟨h,centerUhi,centerVlo,centerVhi⟩)
  have sum : (7/10)*(A.c+A.s) ≤ 1 := by
    nlinarith only [A.unit_normal,sq_nonneg (A.c-A.s),
      sq_nonneg ((7/10)*(A.c+A.s)-1)]
  have topUlo : A.loU < A.c*(12/5)+A.s*3 := by
    linarith only [t.1,hc,hs]
  have topUhi : A.c*(12/5)+A.s*3 < A.loU+A.side := by
    linarith only [centerU,sum,order,ha]
  have topVlo : A.loV < -A.s*(12/5)+A.c*3 := by
    linarith only [q.2.2.1,hc,order]
  have topV : A.loV+A.side ≤ -A.s*(12/5)+A.c*3 :=
    le_of_not_gt (fun h => missingTop ⟨topUlo,topUhi,topVlo,h⟩)
  have rInside : R.Inside (60731/20000) (223/100) := by
    convert inside_segment R (1543/500) 2 3 (12/5) (23/40)
      rMarker rPoint (by norm_num) (by norm_num) using 1 <;> norm_num
  have sectorProduct := mul_nonneg (sub_nonneg.mpr steep)
    (show 0 ≤ A.s+(13/100)*A.c by linarith only [hs,hc])
  have projectedSquare : ((20731/20000)*A.c+(23/100)*A.s)^2 ≤ 1 := by
    nlinarith only [sectorProduct,A.unit_normal,mul_nonneg hc.le hs,
      sq_nonneg A.c]
  have projected : (20731/20000)*A.c+(23/100)*A.s ≤ 1 := by
    nlinarith only [projectedSquare,
      sq_nonneg ((20731/20000)*A.c+(23/100)*A.s-1)]
  have fromTop := short_projections A (12731/20000) (-77/100) (by norm_num)
  have aInside : A.Inside (60731/20000) (223/100) := by
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [t.1,hc,order]
    · linarith only [centerU,projected,ha]
    · linarith only [topV,fromTop.2.2.1,ha]
    · linarith only [p.2.2.2,hc,hs]
  exact apart _ _ ⟨aInside,rInside⟩

/-- Both genuine neighboring wall segments are retained. If the center
escapes, a positive face frame must lie in one of the two stated sectors
near an axis. This conclusion does not exclude those remaining sectors. -/
theorem angle_alternatives (A R T : OpenSquare) (ha : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (t : A.Inside (47/20) (47/20))
    (missingRight : ¬ A.Inside 3 (12/5))
    (missingTop : ¬ A.Inside (12/5) 3)
    (rMarker : R.Inside (1543/500) 2) (rPoint : R.Inside 3 (12/5))
    (tMarker : T.Inside 2 (1543/500)) (tPoint : T.Inside (12/5) 3)
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (apartTop : ∀ x y, ¬ (A.Inside x y ∧ T.Inside x y))
    (missing : ¬ A.Inside 2 2) :
    A.s < (16/25)*A.c ∨ A.c < (16/25)*A.s := by
  by_cases order : A.s ≤ A.c
  · left
    apply lt_of_not_ge
    intro steep
    exact missing (shallow_center A R ha hc hs order steep p q t
      missingTop rMarker rPoint ar)
  · right
    apply lt_of_not_ge
    intro steep
    have swapped := shallow_center (pullSwap A) (pullSwap T) ha
      (by dsimp [pullSwap]; linarith only [hc,lt_of_not_ge order]) hc.le
      (by dsimp [pullSwap]; exact (lt_of_not_ge order).le) steep
      ((inside_pullSwap A _ _).mpr q) ((inside_pullSwap A _ _).mpr p)
      ((inside_pullSwap A _ _).mpr t)
      (fun h => missingRight ((inside_pullSwap A _ _).mp h))
      ((inside_pullSwap T _ _).mpr tMarker) ((inside_pullSwap T _ _).mpr tPoint)
      (fun x y h => apartTop y x ⟨(inside_pullSwap A x y).mp h.1,
        (inside_pullSwap T x y).mp h.2⟩)
    exact missing ((inside_pullSwap A _ _).mp swapped)

#print axioms shallow_center
#print axioms angle_alternatives
end N12Compact.CentralEscapeSegment

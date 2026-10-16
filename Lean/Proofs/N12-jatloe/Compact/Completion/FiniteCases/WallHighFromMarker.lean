import Compact.Geometry.WallLowerReach
import Compact.Geometry.ClosedFrames

/-! A wall owner's missing upper central marker supplies the alternative
previously handled by a missing inward auxiliary point. Thus the wall
advance to 2.56 retains the full true inward-ownership alternative. -/
namespace N12Compact.FiniteCases.WallHighFromMarker
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem inward_point (q : OpenSquare) (side : 1<q.side)
    (hc : 0≤q.c) (hs : 0≤q.s)
    (marker : q.Inside (457/500) 2) (high : q.Inside 1 (12/5))
    (inward : q.Inside (87/50) 2)
    (missingLow : ¬q.Inside 1 (87/50))
    (missingCentral : ¬q.Inside (33/20) (47/20)) : q.Inside 1 (64/25) := by
  have tUlo : q.loU<q.c*(33/20)+q.s*(47/20) := by
    linarith only [marker.1,hc,hs]
  have tVlo : q.loV< -q.s*(33/20)+q.c*(47/20) := by
    linarith only [inward.2.2.1,hc,hs]
  have tVhi : -q.s*(33/20)+q.c*(47/20)<q.loV+q.side := by
    linarith only [high.2.2.2,hc,hs]
  have topFace : q.loU+q.side≤q.c*(33/20)+q.s*(47/20) :=
    le_of_not_gt (fun upper => missingCentral ⟨tUlo,upper,tVlo,tVhi⟩)
  have gap := (short_projections q (13/20) (61/100) (by norm_num)).2.1
  have wUlo : q.loU<q.c+q.s*(87/50) := by
    linarith only [topFace,gap,side]
  have wUhi : q.c+q.s*(87/50)<q.loU+q.side := by
    linarith only [high.2.1,hs]
  have wVhi : -q.s+q.c*(87/50)<q.loV+q.side := by
    linarith only [marker.2.2.2,hc,hs]
  have lowerFace : -q.s+q.c*(87/50)≤q.loV := by
    apply le_of_not_gt
    intro lower
    apply missingLow
    exact ⟨by simpa only [mul_one] using wUlo,
      by simpa only [mul_one] using wUhi,
      by simpa only [mul_one] using lower,
      by simpa only [mul_one] using wVhi⟩
  have sector : 37*q.s<13*q.c := by
    linarith only [lowerFace,inward.2.2.1]
  have cosine : q.c≤1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,hc]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,hc,hs]
  · linarith only [inward.2.1,sector,hc]
  · linarith only [high.2.2.1,hc]
  · linarith only [lowerFace,side,cosine]

/-- No assumption is made about whether the wall owns its inward elbow.
The upper central marker belongs to another actual square in applications. -/
theorem point (q : OpenSquare) (side : 1<q.side) (box : InsideContainer q)
    (marker : q.Inside (457/500) 2) (high : q.Inside 1 (12/5))
    (missingLow : ¬q.Inside 1 (87/50))
    (missingCentral : ¬q.Inside (33/20) (47/20)) : q.Inside 1 (64/25) := by
  by_cases inward : q.Inside (87/50) 2
  · obtain ⟨r,hc,hs,shape,inside,_⟩ := ClosedFrames.positive_frame q
    exact (inside _ _).mp (inward_point r (by simpa only [shape] using side) hc.le hs
      ((inside _ _).mpr marker) ((inside _ _).mpr high) ((inside _ _).mpr inward)
      (fun h => missingLow ((inside _ _).mp h))
      (fun h => missingCentral ((inside _ _).mp h)))
  · exact WallLowerReach.point q side box marker high missingLow inward

#print axioms point
end N12Compact.FiniteCases.WallHighFromMarker

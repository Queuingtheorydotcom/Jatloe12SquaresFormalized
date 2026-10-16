import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! A paired upper-left corner owner that also owns the northwest central
marker reaches height 2.914 on the vertical unit line. The genuine omitted
top-wall marker removes the sole remaining face in the negative sector.
This is a local all-orientation theorem, with no inferred ownership budget. -/
namespace N12Compact.FiniteCases.MergedCornerPoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (left : q.Inside (457/500) 3)
    (top : q.Inside 1 (1543/500))
    (central : q.Inside (33/20) (47/20)) :
    q.Inside 1 (1457/500) := by
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [left.1,order]
  · linarith only [top.2.1,hs]
  · linarith only [central.2.2.1,hc,hs]
  · linarith only [left.2.2.2,hc,hs]

private theorem negative (q : OpenSquare)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (side : 1 < q.side)
    (left : q.Inside (457/500) 3)
    (top : q.Inside 1 (1543/500))
    (central : q.Inside (33/20) (47/20))
    (topMissing : ¬ q.Inside 2 (1543/500)) :
    q.Inside 1 (1457/500) := by
  have sum : q.c-q.s ≤ 3/2 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c+q.s),
      sq_nonneg (q.c-q.s-3/2)]
  have span : -q.s+(43/250)*q.c ≤ 1 := by
    linarith only [sum,order]
  have lowerV : q.loV < -q.s+q.c*(1457/500) := by
    apply lt_of_not_ge
    intro missing
    apply topMissing
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [left.1,order,hc]
    · linarith only [central.2.1,central.2.2.1,missing,hc]
    · linarith only [top.2.2.1,hs]
    · linarith only [missing,span,side]
  refine ⟨?_,?_,by simpa only [mul_one] using lowerV,?_⟩
  · linarith only [left.1,hc,hs]
  · linarith only [central.2.1,hc,hs]
  · linarith only [top.2.2.2,hc]

/-- The original square and every real orientation, including either zero
angle endpoint. The missing point must come from an actual foreign owner. -/
theorem upper_left (q : OpenSquare) (side : 1 < q.side)
    (left : q.Inside (457/500) 3)
    (top : q.Inside 1 (1543/500))
    (central : q.Inside (33/20) (47/20))
    (topMissing : ¬ q.Inside 2 (1543/500)) :
    q.Inside 1 (1457/500) := by
  obtain ⟨r,hc,canonical,same,inside,_⟩ := ClosedFrames.canonical_frame q
  have leftR := (inside _ _).mpr left
  have topR := (inside _ _).mpr top
  have centralR := (inside _ _).mpr central
  by_cases positiveS : 0 ≤ r.s
  · exact (inside _ _).mp (positive r hc positiveS
      (by simpa only [abs_of_nonneg positiveS] using canonical)
      leftR topR centralR)
  · have negativeS : r.s ≤ 0 := (lt_of_not_ge positiveS).le
    exact (inside _ _).mp (negative r hc negativeS
      (by simpa only [abs_of_nonpos negativeS] using canonical)
      (by simpa only [same] using side) leftR topR centralR
      (fun h => topMissing ((inside _ _).mp h)))

#print axioms upper_left
end N12Compact.FiniteCases.MergedCornerPoint

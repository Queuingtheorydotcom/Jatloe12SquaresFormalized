import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! A complete mixed top elbow also owns the top inner endpoint. The
vertical left barrier contributes one actual point, while the right
barrier contributes one. Both canonical signs are retained. -/
namespace N12Compact.FiniteCases.TopElbowCompletion
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (hc : 0<q.c) (hs : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (47/20) (47/20))
    (top : q.Inside (12/5) 3) (elbow : q.Inside (113/50) 2)
    (missingLeft : ¬q.Inside 2 (12/5))
    (missingRight : ¬q.Inside 3 (12/5)) : q.Inside (113/50) 3 := by
  have cosine : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,hc]
  have llUhi : 2*q.c+(12/5)*q.s<q.loU+q.side := by
    linarith only [marker.2.1,hc,order]
  have llVlo : q.loV< -2*q.s+(12/5)*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have llVhi : -2*q.s+(12/5)*q.c<q.loV+q.side := by
    linarith only [top.2.2.2,hc,order]
  have leftFace : 2*q.c+(12/5)*q.s≤q.loU :=
    le_of_not_gt (fun u => missingLeft ⟨u,llUhi,llVlo,llVhi⟩)
  have lrUlo : q.loU<3*q.c+(12/5)*q.s := by
    linarith only [marker.1,hc,hs]
  have lrUhi : 3*q.c+(12/5)*q.s<q.loU+q.side := by
    linarith only [leftFace,side,cosine]
  have lrVhi : -3*q.s+(12/5)*q.c<q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs]
  have rightFace : -3*q.s+(12/5)*q.c≤q.loV :=
    le_of_not_gt (fun v => missingRight ⟨lrUlo,lrUhi,v,lrVhi⟩)
  have short := (short_projections q (-(37/50)) (3/5) (by norm_num)).2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [elbow.1,hs]
  · linarith only [top.2.1,hc]
  · linarith only [elbow.2.2.1,hc]
  · linarith only [rightFace,side,short]

private theorem nonpositive (q : OpenSquare) (side : 1<q.side)
    (hc : 0<q.c) (hs : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (47/20) (47/20))
    (top : q.Inside (12/5) 3) (elbow : q.Inside (113/50) 2)
    (missingRight : ¬q.Inside 3 (12/5)) : q.Inside (113/50) 3 := by
  have lrUlo : q.loU<3*q.c+(12/5)*q.s := by
    linarith only [marker.1,hc,order]
  have lrVlo : q.loV< -3*q.s+(12/5)*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have lrVhi : -3*q.s+(12/5)*q.c<q.loV+q.side := by
    linarith only [top.2.2.2,order]
  have rightFace : q.loU+q.side≤3*q.c+(12/5)*q.s :=
    le_of_not_gt (fun u => missingRight ⟨lrUlo,u,lrVlo,lrVhi⟩)
  have short := (short_projections q (37/50) (-(3/5)) (by norm_num)).2.1
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [rightFace,side,short]
  · linarith only [elbow.2.1,hs]
  · linarith only [elbow.2.2.1,hc]
  · linarith only [top.2.2.2,hs]

/-- The left absences come from one actual owner's vertical segment in
applications. The inward endpoint is never silently replaced by the top one. -/
theorem point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20))
    (top : q.Inside (12/5) 3) (elbow : q.Inside (113/50) 2)
    (missingLeft : ¬q.Inside 2 (12/5))
    (missingRight : ¬q.Inside 3 (12/5)) : q.Inside (113/50) 3 := by
  obtain ⟨r,hc,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame q
  have size : 1<r.side := by simpa only [shape] using side
  have m := (inside _ _).mpr marker
  have t := (inside _ _).mpr top
  have e := (inside _ _).mpr elbow
  have right : ¬r.Inside 3 (12/5) := fun h => missingRight ((inside _ _).mp h)
  by_cases sign : 0≤r.s
  · exact (inside _ _).mp (positive r size hc sign
      (by simpa only [abs_of_nonneg sign] using canonical) m t e
      (fun h => missingLeft ((inside _ _).mp h)) right)
  · have negative : r.s≤0 := (lt_of_not_ge sign).le
    exact (inside _ _).mp (nonpositive r size hc negative
      (by simpa only [abs_of_nonpos negative] using canonical) m t e
      right)

#print axioms point
end N12Compact.FiniteCases.TopElbowCompletion

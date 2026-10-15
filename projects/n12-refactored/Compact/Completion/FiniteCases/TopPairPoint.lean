import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! A NW-to-top-right pair reaches the top-left point unless it contains
the neighboring central crosspoint. Two short projections cover the full
orientation circle; no angle cells or auxiliary budget are used. -/
namespace N12Compact.FiniteCases.TopPairPoint
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (hc : 0<q.c) (hs : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (-(7/20)) (-(13/20))) (top : q.Inside (2/5) 0)
    (missingNE : ¬q.Inside (7/20) (-(13/20)))
    (missingCross : ¬q.Inside 0 (-(1/2))) : q.Inside (-(2/5)) 0 := by
  have neUlo : q.loU<q.c*(7/20)+q.s*(-(13/20)) := by
    linarith only [marker.1,hc]
  have neUhi : q.c*(7/20)+q.s*(-(13/20))<q.loU+q.side := by
    linarith only [top.2.1,hc,hs]
  have neVhi : -q.s*(7/20)+q.c*(-(13/20))<q.loV+q.side := by
    linarith only [marker.2.2.2,hs]
  have lower : -q.s*(7/20)+q.c*(-(13/20))≤q.loV :=
    le_of_not_gt (fun v => missingNE ⟨neUlo,neUhi,v,neVhi⟩)
  have short := (short_projections q (-(3/4)) (13/20) (by norm_num)).2.2.2
  have fUhi : q.c*(-(2/5))+q.s*0<q.loU+q.side := by
    linarith only [top.2.1,hc]
  have fVlo : q.loV< -q.s*(-(2/5))+q.c*0 := by
    linarith only [marker.2.2.1,hc,hs]
  have fVhi : -q.s*(-(2/5))+q.c*0<q.loV+q.side := by
    linarith only [lower,short,side]
  by_contra missing
  have face : q.c*(-(2/5))≤q.loU := by
    apply le_of_not_gt
    intro u
    exact missing ⟨by simpa only [mul_zero,add_zero] using u,fUhi,fVlo,fVhi⟩
  have narrow : 13*q.s<q.c := by linarith only [face,marker.1]
  apply missingCross
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,hc,hs]
  · linarith only [top.2.1,hc,hs]
  · linarith only [marker.2.2.1,narrow,hc]
  · linarith only [top.2.2.2,hc,order]

private theorem nonpositive (q : OpenSquare) (side : 1<q.side)
    (hc : 0<q.c) (hs : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (-(7/20)) (-(13/20))) (top : q.Inside (2/5) 0)
    (missingNE : ¬q.Inside (7/20) (-(13/20))) : q.Inside (-(2/5)) 0 := by
  have neUlo : q.loU<q.c*(7/20)+q.s*(-(13/20)) := by
    linarith only [marker.1,hc]
  have neVlo : q.loV< -q.s*(7/20)+q.c*(-(13/20)) := by
    linarith only [marker.2.2.1,hs]
  have neVhi : -q.s*(7/20)+q.c*(-(13/20))<q.loV+q.side := by
    linarith only [top.2.2.2,hc,hs]
  have upper : q.loU+q.side≤q.c*(7/20)+q.s*(-(13/20)) :=
    le_of_not_gt (fun u => missingNE ⟨neUlo,u,neVlo,neVhi⟩)
  have short := (short_projections q (3/4) (-(13/20)) (by norm_num)).2.1
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [upper,short,side]
  · linarith only [top.2.1,hc]
  · linarith only [marker.2.2.1,hc,order]
  · linarith only [top.2.2.2,hs]

theorem point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (33/20) (47/20)) (top : q.Inside (12/5) 3)
    (missingNE : ¬q.Inside (47/20) (47/20))
    (missingCross : ¬q.Inside 2 (5/2)) : q.Inside (8/5) 3 := by
  let shifted := q.translated 2 3
  have m : shifted.Inside (-(7/20)) (-(13/20)) := by
    norm_num [shifted,inside_translated_iff]; exact marker
  have t : shifted.Inside (2/5) 0 := by
    norm_num [shifted,inside_translated_iff]; exact top
  have ne : ¬shifted.Inside (7/20) (-(13/20)) := by
    norm_num [shifted,inside_translated_iff]; exact missingNE
  have cross : ¬shifted.Inside 0 (-(1/2)) := by
    norm_num [shifted,inside_translated_iff]; exact missingCross
  obtain ⟨r,hc,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame shifted
  have size : 1<r.side := by simpa only [shape] using side
  have result : shifted.Inside (-(2/5)) 0 := by
    by_cases sign : 0≤r.s
    · exact (inside _ _).mp (positive r size hc sign
        (by simpa only [abs_of_nonneg sign] using canonical)
        ((inside _ _).mpr m) ((inside _ _).mpr t)
        (fun h => ne ((inside _ _).mp h)) (fun h => cross ((inside _ _).mp h)))
    · have negative : r.s≤0 := (lt_of_not_ge sign).le
      exact (inside _ _).mp (nonpositive r size hc negative
        (by simpa only [abs_of_nonpos negative] using canonical)
        ((inside _ _).mpr m) ((inside _ _).mpr t) (fun h => ne ((inside _ _).mp h)))
  norm_num [shifted,inside_translated_iff] at result
  exact result

#print axioms point
end N12Compact.FiniteCases.TopPairPoint

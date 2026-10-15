import Compact.Geometry.MergedLeftEscapeAux
import Compact.Geometry.MergedLeftNegative

/-! A merged adjacent central pair contains the container center once its
two inward escape routes are blocked by actual owners. The wall retains
its full square, containment, common side, and interior disjointness. -/
namespace N12Compact.FiniteCases.MergedLeftCenter
open S12 S12Pilot
set_option Elab.async false

theorem point (A L : OpenSquare) (side : 1<A.side)
    (same : A.side=L.side) (box : InsideContainer L)
    (southwest : A.Inside (33/20) (33/20))
    (northwest : A.Inside (33/20) (47/20))
    (leftLow : ¬A.Inside 1 (87/50))
    (leftHigh : ¬A.Inside 1 (113/50))
    (inwardLow : ¬A.Inside 2 (87/50))
    (bottom : ¬A.Inside (8/5) 1)
    (top : ¬A.Inside (8/5) 3)
    (wallMarker : L.Inside (457/500) 2)
    (wallHigh : L.Inside 1 (12/5))
    (apart : ∀ x y, ¬(A.Inside x y ∧ L.Inside x y)) : A.Inside 2 2 := by
  obtain ⟨q,hc,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame A
  have size : 1<q.side := by simpa only [shape] using side
  have sw := (inside _ _).mpr southwest
  have nw := (inside _ _).mpr northwest
  have low : ¬q.Inside 1 (87/50) := fun h => leftLow ((inside _ _).mp h)
  have high : ¬q.Inside 1 (113/50) := fun h => leftHigh ((inside _ _).mp h)
  by_cases sign : 0≤q.s
  · by_contra center
    have escaped := MergedLeftEscapeAux.inward q size hc sign
      (by simpa only [abs_of_nonneg sign] using canonical) sw nw
      (fun h => center ((inside _ _).mp h)) low high
      (fun h => bottom ((inside _ _).mp h))
    exact inwardLow ((inside _ _).mp escaped)
  · have negative : q.s≤0 := (lt_of_not_ge sign).le
    exact (inside _ _).mp (MergedLeftNegative.point q L size (shape.trans same) box
      hc negative (by simpa only [abs_of_nonpos negative] using canonical)
      sw nw low high (fun h => top ((inside _ _).mp h)) wallMarker wallHigh
      (fun x y h => apart x y ⟨(inside _ _).mp h.1,h.2⟩))

#print axioms point
end N12Compact.FiniteCases.MergedLeftCenter

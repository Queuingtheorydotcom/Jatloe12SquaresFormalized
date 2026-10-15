import Compact.Geometry.FourSquareRHigh
import Compact.Geometry.FourSquareANarrow
import S12.Container

/-! The forced A point from actual neighbouring squares, in every orientation.
All closed points and missing points are the original template's premises. -/

namespace N12Compact.FourSquareAAll

open S12 S12Pilot FourSquareAnchors

theorem point (A B R : OpenSquare) (ha : 1 < A.side) (hr : 1 < R.side)
    (boxR : InsideContainer R)
    (hP : ClosedInside A 2 (113/50)) (hQ : ClosedInside A (113/50) 2)
    (hT : ClosedInside A (47/20) (47/20))
    (hF : ¬ A.Inside (33/20) (33/20)) (hG : ¬ A.Inside (47/20) (33/20))
    (b₀ : ClosedInside B (33/20) (47/20))
    (r₀ : ClosedInside R 3 (12/5)) (r₁ : ClosedInside R (1543/500) 2)
    (rW : ¬ R.Inside (81/25) (187/100))
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 (5/2) := by
  have rHigh := FourSquareRHigh.right_point R A hr boxR r₁ r₀ rW hQ
    (fun x y h => ar x y ⟨h.2,h.1⟩)
  have bOutside := ClosedPointExclusion.outside_of_closed A B _ _ ab b₀
  have rOutside := ClosedPointExclusion.outside_of_closed A R _ _ ar r₀
  have rHighOutside : ¬ A.Inside 3 (5/2) := fun h => ar _ _ ⟨h,rHigh⟩
  obtain ⟨q,hc,hs,hside,hi,hcl⟩ := ClosedFrames.positive_frame A
  have qPoint := FourSquareANarrow.point_of_higher_R q (by simpa only [hside] using ha)
    hc hs ((hcl _ _).mpr hP) ((hcl _ _).mpr hQ) ((hcl _ _).mpr hT)
    (fun h => hF ((hi _ _).mp h)) (fun h => hG ((hi _ _).mp h))
    (fun h => bOutside ((hi _ _).mp h)) (fun h => rOutside ((hi _ _).mp h))
    (fun h => rHighOutside ((hi _ _).mp h))
  exact (hi _ _).mp qPoint

#print axioms point
end N12Compact.FourSquareAAll

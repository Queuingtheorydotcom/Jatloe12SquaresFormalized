import Compact.Geometry.CornerInwardPoint

/-! Exact corner-square coupling in the negative canonical B sector.
The bound depends on the actual common side, rather than replacing the
corner square by the weaker fixed point (1,3). -/
namespace N12Compact.C849NegativeCorner

open S12 S12Pilot FourSquareAnchors

theorem lower_face (B E : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (canonical : -B.s ≤ B.c)
    (same : E.side = B.side) (ha : 1 < B.side)
    (size : B.side ≤ 1001/1000) (boxE : InsideContainer E)
    (eP : E.Inside 1 (1543/500)) (eQ : E.Inside (457/500) 3)
    (bT : B.Inside (33/20) (47/20))
    (bP : ClosedInside B (8/5) 3)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ E.Inside x y)) :
    B.side*(B.c-B.s)+4*B.s ≤ B.loU := by
  have missing := CornerInwardPoint.outside_upper_left B E
    (by simpa only [same] using ha) (by simpa only [same] using size)
    boxE eP eQ apart
  rw [same] at missing
  have sumNonneg : 0 ≤ B.c+B.s := by linarith only [canonical]
  have vGap := mul_nonneg
    (show 0 ≤ 33/20-B.side by linarith only [size]) sumNonneg
  have lowerV : B.loV < -B.s*B.side+B.c*(4-B.side) := by
    nlinarith only [bT.2.2.1,vGap]
  have uGap₀ := mul_nonneg (show 0 ≤ B.side-1 by linarith only [ha]) sumNonneg
  have uGap₁ := mul_pos bc
    (show 0 < 13/5-2*B.side by linarith only [size])
  have upperU : B.c*B.side+B.s*(4-B.side) < B.loU+B.side := by
    nlinarith only [bP.2.1,uGap₀,uGap₁]
  have vGap₀ := mul_nonneg
    (show 0 ≤ 8/5-B.side by linarith only [size]) (neg_nonneg.mpr bs)
  have vGap₁ := mul_pos (sub_pos.mpr ha) bc
  have upperV : -B.s*B.side+B.c*(4-B.side) < B.loV+B.side := by
    nlinarith only [bP.2.2.2,vGap₀,vGap₁]
  apply le_of_not_gt
  intro lowerU
  exact missing ⟨by nlinarith only [lowerU],upperU,lowerV,upperV⟩

#print axioms lower_face

end N12Compact.C849NegativeCorner

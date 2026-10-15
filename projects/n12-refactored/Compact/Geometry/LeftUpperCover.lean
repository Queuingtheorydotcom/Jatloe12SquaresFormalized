import Compact.Geometry.ClosedFrames
import Compact.Geometry.FourSquareBLBridge
import Compact.Geometry.FourSquareLongitudinal

/-! A wall square with the original left-side anchors contains one of two
fixed points.  The conclusion uses the actual open square, not an enclosure.
This is a reusable reduction for the unfinished 849/851 endgame; it does
not assert that those complete packing cases have been excluded. -/

namespace N12Compact.LeftUpperCover

open S12 S12Pilot FourSquareAnchors

/-- The lower-U alternative for the original missing wall point forces
the lower of the two candidate points strictly inside. -/
theorem low_of_lower_U (L : OpenSquare)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c) (ha : 1 < L.side)
    (left : ClosedInside L (457/500) 2)
    (top : ClosedInside L 1 (12/5))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (below : L.c*(19/25)+L.s*(187/100) ≤ L.loU) :
    L.Inside (7/5) (5/2) := by
  have bounds := abs_le.mp lsc
  have pLowerU : L.loU < L.c*(33/20)+L.s*(33/20) := by
    linarith only [left.1, bounds.2, lc]
  have pUpperU : L.c*(33/20)+L.s*(33/20) < L.loU+L.side := by
    have short := (short_projections L (89/100) (-(11/50)) (by norm_num)).2.1
    linarith only [below, short, ha]
  have pUpperV : -L.s*(33/20)+L.c*(33/20) < L.loV+L.side := by
    linarith only [top.2.2.2, bounds.1, lc]
  have pBelow : -L.s*(33/20)+L.c*(33/20) ≤ L.loV :=
    le_of_not_gt (fun hp => missingRight ⟨pLowerU,pUpperU,hp,pUpperV⟩)
  have shortU := (short_projections L (16/25) (63/100) (by norm_num)).2.1
  have shortV := (short_projections L (-(1/4)) (17/20) (by norm_num)).2.2.2
  exact ⟨by linarith only [top.1, bounds.1, lc],
    by linarith only [below, shortU, ha],
    by linarith only [left.2.2.1, bounds.2, lc],
    by linarith only [pBelow, shortV, ha]⟩

private theorem high_upper_U (L : OpenSquare)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c) (ha : 1 < L.side)
    (box : InsideContainer L)
    (left : ClosedInside L (457/500) 2)
    (below : -L.s*(19/25)+L.c*(187/100) ≤ L.loV) :
    L.c+L.s*(283/100) < L.loU+L.side := by
  have walls := FourSquareBLBridge.left_upper_bounds L lc box left below
  have unit := L.unit_normal
  have cOne : L.c ≤ 1 := by nlinarith only [unit, sq_nonneg L.s]
  have cSeven : 7/10 ≤ L.c := by
    have square := (sq_le_sq₀ (abs_nonneg L.s) lc.le).mpr lsc
    rw [sq_abs] at square
    nlinarith only [unit, square, lc, sq_nonneg (L.c-7/10)]
  by_cases sign : 0 ≤ L.s
  · have margin := FourSquareLongitudinal.positive_slope_margin L.c L.s
      lc sign (abs_le.mp lsc).2 unit
    have product := mul_nonneg sign margin.le
    have identity :
        (L.c+L.s-L.c^2-(24/25)*L.c*L.s-(19/25)*L.s^2)*(1+L.c) =
          L.s*((1-(19/25)*L.s)*(1+L.c)+L.s*L.c-
            (24/25)*L.c*(1+L.c)) := by
      linear_combination -L.c*unit
    have nonnegative : 0 ≤ L.c+L.s-L.c^2-
        (24/25)*L.c*L.s-(19/25)*L.s^2 :=
      nonneg_of_mul_nonneg_right (by rw [mul_comm,identity]; exact product)
        (by linarith only [lc])
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < L.c+L.s by linarith only [lc,sign])
    have clear : (L.side*(1+L.s/L.c)+(187/100)*L.s-
        (19/25)*L.s^2/L.c)*L.c =
        L.side*(L.c+L.s)+(187/100)*L.s*L.c-(19/25)*L.s^2 := by
      field_simp [ne_of_gt lc] <;> ring
    have scaled := mul_le_mul_of_nonneg_right (walls.1 sign) lc.le
    rw [clear] at scaled
    nlinarith only [scaled,nonnegative,strict]
  · have sign' : L.s ≤ 0 := le_of_not_ge sign
    have sOne : -L.s ≤ 1 := by
      nlinarith only [unit, sq_nonneg L.c]
    have halfSquare : L.s^2/2 ≤ 1-L.c := by
      nlinarith only [unit,sq_nonneg (1-L.c)]
    have centerProduct := mul_nonneg
      (sub_nonneg.mpr cSeven) (sub_nonneg.mpr cOne)
    have mixedProduct := mul_nonneg
      (sub_nonneg.mpr cSeven) (neg_nonneg.mpr sign')
    have squareBound := mul_nonneg (neg_nonneg.mpr sign')
      (show 0 ≤ 1+L.s by linarith only [sOne])
    have nonnegative : 0 ≤ L.c*(1-L.c)-(457/500)*L.s^2-
        (83/100)*L.c*L.s := by
      nlinarith only [halfSquare,centerProduct,mixedProduct,squareBound,sign']
    have strict := mul_pos (sub_pos.mpr ha) lc
    have clear : (L.side-(457/500)*L.s^2/L.c+2*L.s)*L.c =
        L.side*L.c-(457/500)*L.s^2+2*L.s*L.c := by
      field_simp [ne_of_gt lc] <;> ring
    have scaled := mul_le_mul_of_nonneg_right (walls.2 sign') lc.le
    rw [clear] at scaled
    nlinarith only [scaled,nonnegative,strict]

/-- In a canonical face frame, avoiding the lower candidate forces the
upper candidate and identifies the actual missing-point face. -/
theorem high_of_not_low (L : OpenSquare)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c) (ha : 1 < L.side)
    (box : InsideContainer L)
    (left : ClosedInside L (457/500) 2)
    (top : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20))
    (notLow : ¬ L.Inside (7/5) (5/2)) :
    L.Inside 1 (283/100) ∧
      -L.s*(19/25)+L.c*(187/100) ≤ L.loV := by
  have bounds := abs_le.mp lsc
  have wUpperU : L.c*(19/25)+L.s*(187/100) < L.loU+L.side := by
    linarith only [left.2.1,bounds.1,lc]
  have wUpperV : -L.s*(19/25)+L.c*(187/100) < L.loV+L.side := by
    linarith only [top.2.2.2,bounds.2,lc]
  have wLowerU : L.loU < L.c*(19/25)+L.s*(187/100) := by
    apply lt_of_not_ge
    intro below
    exact notLow (low_of_lower_U L lc lsc ha left top missingRight below)
  have below : -L.s*(19/25)+L.c*(187/100) ≤ L.loV :=
    le_of_not_gt (fun hp => missingLow ⟨wLowerU,wUpperU,hp,wUpperV⟩)
  have lowLowerU : L.loU < L.c*(7/5)+L.s*(5/2) := by
    linarith only [top.1,bounds.1,lc]
  have lowLowerV : L.loV < -L.s*(7/5)+L.c*(5/2) := by
    linarith only [left.2.2.1,bounds.2,lc]
  have lowUpperV : -L.s*(7/5)+L.c*(5/2) < L.loV+L.side := by
    have short := (short_projections L (16/25) (63/100) (by norm_num)).2.2.2
    linarith only [below,short,ha]
  have lowAbove : L.loU+L.side ≤ L.c*(7/5)+L.s*(5/2) :=
    le_of_not_gt (fun hp => notLow ⟨lowLowerU,hp,lowLowerV,lowUpperV⟩)
  have upperU := high_upper_U L lc lsc ha box left below
  have shortU := (short_projections L (2/5) (-(33/100)) (by norm_num)).2.1
  have shortV := (short_projections L (6/25) (24/25) (by norm_num)).2.2.2
  refine ⟨?_,below⟩
  exact ⟨by linarith only [lowAbove,shortU,ha],
    by simpa only [mul_one] using upperU,
    by linarith only [top.2.2.1,lc],
    by linarith only [below,shortV,ha]⟩

/-- The physical wall square contains (1.4,2.5) or (1,2.83), at every
orientation. Closed anchors are sufficient; both conclusions are strict. -/
theorem cover (L : OpenSquare) (ha : 1 < L.side)
    (box : InsideContainer L)
    (left : ClosedInside L (457/500) 2)
    (top : ClosedInside L 1 (12/5))
    (missingLow : ¬ L.Inside (19/25) (187/100))
    (missingRight : ¬ L.Inside (33/20) (33/20)) :
    L.Inside (7/5) (5/2) ∨ L.Inside 1 (283/100) := by
  by_cases low : L.Inside (7/5) (5/2)
  · exact Or.inl low
  · obtain ⟨q,hc,hsc,hside,hi,hcl⟩ := ClosedFrames.canonical_frame L
    have high := high_of_not_low q hc hsc (by simpa only [hside] using ha)
      (fun x y hp => box x y ((hi x y).mp hp))
      ((hcl _ _).mpr left) ((hcl _ _).mpr top)
      (fun hp => missingLow ((hi _ _).mp hp))
      (fun hp => missingRight ((hi _ _).mp hp))
      (fun hp => low ((hi _ _).mp hp))
    exact Or.inr ((hi _ _).mp high.1)

#print axioms cover
end N12Compact.LeftUpperCover

import Compact.Geometry.FourSquareBNegative

/-! Complete negative-canonical B exclusion in the original square model.
A is used only through its already proved occupied points on the cut and
at (2,2.5). The side lengths of B and L need not be equal. -/

namespace N12Compact.FourSquareBNegativeCorner

open S12 S12Pilot FourSquareAnchors ThreeSquare SectionCapacity LongSectionGeometry
open FourSquareBNegative FourSquareBLBridge

theorem center_above_radius (B : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (ha : 1 < B.side) (cap : B.side ≤ 1001/1000)
    (top : ClosedInside B (8/5) 3) (short : ¬ LongSection B (12/5)) :
    12/5+(B.c-B.s+2*B.c*B.s)/2 < centerY B := by
  have sum : B.c-B.s ≤ 10/7 := by
    nlinarith [B.unit_normal,sq_nonneg (B.c+B.s)]
  have prod : -B.c*B.s ≤ 1/2 := by
    nlinarith [B.unit_normal,sq_nonneg (B.c+B.s)]
  have htop := (abs_le.mp (closed_support B (8/5) 3 0 1 top)).2
  simp only [supportRadius,zero_mul,one_mul,zero_add,neg_zero,
    abs_of_nonpos bs,abs_of_nonneg bc.le] at htop
  have hmul := mul_le_mul_of_nonneg_left cap
    (by linarith only [bc,bs] : 0 ≤ B.c-B.s)
  have low : 12/5-(B.c-B.s+2*B.c*B.s)/2 ≤ centerY B := by
    nlinarith only [htop,hmul,sum,prod]
  apply lt_of_not_ge
  intro high
  apply short
  apply horizontal_long_section B _ ha
  simp only [sectionRadius,abs_of_nonneg bc.le,abs_of_nonpos bs,
    abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos bc.le bs)]
  apply abs_le.mpr
  constructor <;> linarith only [low,high]

/-- A failed section puts the upper V face below the right missing corner. -/
theorem upper_corner (B : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (ha : 1 < B.side) (cap : B.side ≤ 1001/1000)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3) (topRight : ClosedInside B (87/50) 3)
    (missingLeft : ¬ B.Inside 1 (1543/500))
    (missingRight : ¬ B.Inside 2 (1543/500))
    (short : ¬ LongSection B (12/5)) :
    B.loV+B.side ≤ -2*B.s+(1543/500)*B.c := by
  have bc1 : B.c ≤ 1 := by nlinarith [B.unit_normal,sq_nonneg B.s]
  have high := center_above_radius B bc bs bsc ha cap top short
  have pUhi : B.c+B.s*(1543/500) < B.loU+B.side := by
    nlinarith only [top.2.1,bc,bs]
  have pVlo : B.loV < -B.s+B.c*(1543/500) := by
    nlinarith only [bottom.2.2.1,bsc,bc]
  have pMode : B.c+B.s*(1543/500) ≤ B.loU ∨
      B.loV+B.side ≤ -B.s+B.c*(1543/500) := by
    by_cases hu : B.c+B.s*(1543/500) ≤ B.loU
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => missingLeft
        ⟨by simpa only [mul_one] using lt_of_not_ge hu,
          by simpa only [mul_one] using pUhi,
          by simpa only [mul_one] using pVlo,by simpa only [mul_one] using hv⟩))
  have qUlo : B.loU < 2*B.c+B.s*(1543/500) := by
    nlinarith only [topRight.1,bsc,bc]
  have qVlo : B.loV < -2*B.s+B.c*(1543/500) := by
    nlinarith only [bottom.2.2.1,bs,bc]
  have qMode : B.loU+B.side ≤ 2*B.c+B.s*(1543/500) ∨
      B.loV+B.side ≤ -2*B.s+B.c*(1543/500) := by
    by_cases hu : B.loU+B.side ≤ 2*B.c+B.s*(1543/500)
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => missingRight
        ⟨by nlinarith only [qUlo],by nlinarith only [lt_of_not_ge hu],
          by nlinarith only [qVlo],by nlinarith only [hv]⟩))
  have notLeftV : ¬ B.loV+B.side ≤ -B.s+B.c*(1543/500) := by
    intro hv
    have ratio : -300*B.s ≤ 43*B.c := by linarith only [hv,top.2.2.2]
    have square := mul_nonneg (sub_nonneg.mpr ratio)
      (by linarith only [bc,bs] : 0 ≤ 43*B.c-300*B.s)
    have c94 : 47/50 ≤ B.c := by nlinarith only [B.unit_normal,square,bc]
    have cp : -B.c*B.s ≤ 43/300 := by
      have hm := mul_le_mul_of_nonneg_left ratio bc.le
      nlinarith only [hm,B.unit_normal,sq_nonneg B.s]
    have u := mul_le_mul_of_nonpos_left topRight.2.1 bs
    have v := mul_le_mul_of_nonneg_left hv bc.le
    have a := mul_nonneg (by linarith only [ha] : 0 ≤ B.side-1)
      (by linarith only [bsc] : 0 ≤ B.c+B.s)
    have center : centerY B = B.s*(B.loU+B.side/2)+B.c*(B.loV+B.side/2) := rfl
    nlinarith only [u,v,center,B.unit_normal,a,high,c94,cp,sq_nonneg B.s]
  have pLow := pMode.resolve_right notLeftV
  rcases qMode with qu | qv
  · exfalso
    nlinarith only [pLow,qu,ha,bc1]
  · linarith only [qv]

/-- The entire negative canonical branch, with precisely the original
closed points, missing points, wall, and pairwise interior disjointness. -/
theorem exclude (B L : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (haB : 1 < B.side) (cap : B.side ≤ 1001/1000) (haL : 1 < L.side)
    (boxL : InsideContainer L)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3) (topRight : ClosedInside B (87/50) 3)
    (ll : ClosedInside L (457/500) 2) (lt : ClosedInside L 1 (12/5))
    (missingLeft : ¬ B.Inside 1 (1543/500))
    (missingRight : ¬ B.Inside 2 (1543/500))
    (rowMissing : ¬ B.Inside 1 (12/5))
    (targetMissing : ¬ B.Inside 2 (5/2))
    (missing : ¬ L.Inside (19/25) (187/100))
    (missingRightL : ¬ L.Inside (33/20) (33/20))
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y))
    (short : ¬ LongSection B (12/5)) : False := by
  have upperV := upper_corner B bc bs bsc haB cap bottom top topRight
    missingLeft missingRight short
  obtain ⟨upperU,lowerV,height⟩ := forced_faces B bc bs bsc haB bottom top
    rowMissing targetMissing upperV
  obtain ⟨m,n⟩ := right_points B bc bs bsc haB bottom top upperU upperV height
  have labs := abs_le.mp lsc
  have wu : L.c*(19/25)+L.s*(187/100) < L.loU+L.side := by
    nlinarith only [ll.2.1,labs.1,lc]
  have wv : -L.s*(19/25)+L.c*(187/100) < L.loV+L.side := by
    nlinarith only [lt.2.2.2,labs.2,lc]
  have lowV : -L.s*(19/25)+L.c*(187/100) ≤ L.loV := by
    apply le_of_not_gt
    intro above
    have wrong : L.c*(19/25)+L.s*(187/100) ≤ L.loU :=
      le_of_not_gt (fun hu => missing ⟨hu,wu,above,wv⟩)
    exact apart _ _ ⟨m,left_point_of_lower_U L lc lsc haL ll lt missingRightL wrong⟩
  rcases left_cover L lc lsc haL boxL ll lt lowV with lm | ln
  · exact apart _ _ ⟨m,lm⟩
  · exact apart _ _ ⟨n,ln⟩

#print axioms exclude
end N12Compact.FourSquareBNegativeCorner

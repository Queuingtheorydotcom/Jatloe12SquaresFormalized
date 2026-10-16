import Compact.Geometry.FourSquareBLBridge

/-! The negative canonical B branch is eliminated by two common points.
No separating-axis split is needed: B contains M=(1.3,2.4), N=(1,2.68),
whereas the actual left square must contain at least one of them. -/

namespace N12Compact.FourSquareBNegative

open S12 S12Pilot FourSquareAnchors ThreeSquare FourSquareBLBridge
open SectionCapacity LongSectionGeometry

/-- The left wall and W below V force one of two nearby points, retaining
both signs of L's frame. -/
theorem left_cover (L : OpenSquare) (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (ha : 1 < L.side) (box : InsideContainer L)
    (ll : ClosedInside L (457/500) 2) (lt : ClosedInside L 1 (12/5))
    (lowV : -L.s*(19/25)+L.c*(187/100) ≤ L.loV) :
    L.Inside (13/10) (12/5) ∨ L.Inside 1 (67/25) := by
  have labs := abs_le.mp lsc
  have wall := left_wall L lc.le box
  have lc1 : L.c ≤ 1 := by nlinarith [L.unit_normal,sq_nonneg L.s]
  have lc7 : 7/10 ≤ L.c := by
    nlinarith [L.unit_normal,mul_nonneg (by linarith only [labs] : 0 ≤ L.c-L.s)
      (by linarith only [labs] : 0 ≤ L.c+L.s)]
  have cbelow : 1-L.c ≤ (3/5)*L.s^2 := by
    nlinarith [L.unit_normal,mul_nonneg (by linarith : 0 ≤ 1-L.c)
      (by linarith : 0 ≤ L.c-2/3)]
  have nVlo : L.loV < -L.s+L.c*(67/25) := by linarith [lt.2.2.1]
  have nvSpan := (short_projections L (6/25) (81/100) (by norm_num)).2.2.2
  have nVhi : -L.s+L.c*(67/25) < L.loV+L.side := by
    linarith only [lowV,nvSpan,ha]
  have nUhi : L.c+L.s*(67/25) < L.loU+L.side := by
    apply lt_of_not_ge
    intro above
    have target := mul_nonneg lc.le (sub_nonneg.mpr above)
    have strict := mul_pos (sub_pos.mpr ha) lc
    dsimp [centerX] at wall
    by_cases ls : 0 ≤ L.s
    · rw [abs_of_nonneg ls] at wall
      have vl := mul_le_mul_of_nonneg_left lowV ls
      have span := (short_projections L (81/100) (9/25) (by norm_num)).2.1
      have bound := mul_nonneg ls (by linarith only [span] : 0 ≤ 1-(81/100)*L.c-(9/25)*L.s)
      have aa := mul_nonneg ls (by linarith only [ha] : 0 ≤ L.side-1)
      nlinarith only [wall,vl,target,strict,cbelow,bound,aa,L.unit_normal]
    · rw [abs_of_nonpos (le_of_not_ge ls)] at wall
      have vl := mul_le_mul_of_nonpos_left ll.2.2.1 (le_of_not_ge ls)
      have sqbound := mul_nonneg (by linarith only [ls] : 0 ≤ -L.s)
        (by linarith only [labs] : 0 ≤ L.c+L.s)
      have cs := mul_nonpos_of_nonneg_of_nonpos lc.le (le_of_not_ge ls)
      nlinarith only [wall,vl,target,strict,cbelow,sqbound,cs,L.unit_normal]
  by_cases ls : 0 ≤ L.s
  · right
    exact ⟨by linarith [ll.1],by simpa only [mul_one] using nUhi,
      by simpa only [mul_one] using nVlo,by simpa only [mul_one] using nVhi⟩
  · by_cases inside : L.Inside (13/10) (12/5)
    · exact Or.inl inside
    · right
      have mUlo : L.loU < L.c*(13/10)+L.s*(12/5) := by linarith [lt.1]
      have mVlo : L.loV < -L.s*(13/10)+L.c*(12/5) := by linarith [lt.2.2.1]
      have mvSpan := (short_projections L (27/50) (53/100) (by norm_num)).2.2.2
      have mVhi : -L.s*(13/10)+L.c*(12/5) < L.loV+L.side := by
        linarith only [lowV,mvSpan,ha]
      have mUhi : L.loU+L.side ≤ L.c*(13/10)+L.s*(12/5) :=
        le_of_not_gt (fun hu => inside ⟨mUlo,hu,mVlo,mVhi⟩)
      have span := (short_projections L (3/10) (-(7/25)) (by norm_num)).2.1
      have nUlo : L.loU < L.c+L.s*(67/25) := by
        linarith only [mUhi,span,ha]
      exact ⟨by simpa only [mul_one] using nUlo,by simpa only [mul_one] using nUhi,
        by simpa only [mul_one] using nVlo,by simpa only [mul_one] using nVhi⟩

/-- Occupied points at (1,2.4) and (2,2.5) sharpen the negative corner. -/
theorem forced_faces (B : OpenSquare) (bc : 0 < B.c)
    (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c) (ha : 1 < B.side)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (rowMissing : ¬ B.Inside 1 (12/5))
    (targetMissing : ¬ B.Inside 2 (5/2))
    (upperV : B.loV+B.side ≤ -2*B.s+(1543/500)*B.c) :
    B.loU+B.side ≤ 2*B.c+(5/2)*B.s ∧
    -B.s+(12/5)*B.c ≤ B.loV ∧ B.side ≤ -B.s+(343/500)*B.c := by
  have bc1 : B.c ≤ 1 := by nlinarith [B.unit_normal,sq_nonneg B.s]
  have zUlo : B.loU < 2*B.c+B.s*(5/2) := by nlinarith only [bottom.1,bc,bsc]
  have zVlo : B.loV < -2*B.s+B.c*(5/2) := by nlinarith only [bottom.2.2.1,bc,bs]
  have zVhi : -2*B.s+B.c*(5/2) < B.loV+B.side := by
    nlinarith only [top.2.2.2,bc,bsc]
  have zUhi : B.loU+B.side ≤ 2*B.c+B.s*(5/2) :=
    le_of_not_gt (fun hu => targetMissing ⟨by nlinarith only [zUlo],
      by nlinarith only [hu],by nlinarith only [zVlo],by nlinarith only [zVhi]⟩)
  have rUhi : B.c+B.s*(12/5) < B.loU+B.side := by
    nlinarith only [bottom.2.1,bc,bs]
  have rVhi : -B.s+B.c*(12/5) < B.loV+B.side := by
    nlinarith only [top.2.2.2,bc,bs]
  have rUlo : B.loU < B.c+B.s*(12/5) := by
    nlinarith only [zUhi,ha,bc1,bs]
  have rVlo : -B.s+B.c*(12/5) ≤ B.loV :=
    le_of_not_gt (fun hv => rowMissing ⟨by simpa only [mul_one] using rUlo,
      by simpa only [mul_one] using rUhi,by simpa only [mul_one] using hv,
      by simpa only [mul_one] using rVhi⟩)
  exact ⟨by linarith only [zUhi],by linarith only [rVlo],by linarith only [rVlo,upperV]⟩

/-- Both explicit points lie strictly in a negative-corner B. -/
theorem right_points (B : OpenSquare) (bc : 0 < B.c)
    (bs : B.s ≤ 0) (bsc : -B.s ≤ B.c) (ha : 1 < B.side)
    (bottom : ClosedInside B (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (upperU : B.loU+B.side ≤ 2*B.c+(5/2)*B.s)
    (upperV : B.loV+B.side ≤ -2*B.s+(1543/500)*B.c)
    (height : B.side ≤ -B.s+(343/500)*B.c) :
    B.Inside (13/10) (12/5) ∧ B.Inside 1 (67/25) := by
  have bc1 : B.c ≤ 1 := by nlinarith [B.unit_normal,sq_nonneg B.s]
  have bs1 : -B.s ≤ 1 := by nlinarith [B.unit_normal,sq_nonneg B.c]
  have mSpan := (short_projections B (7/10) (343/500) (by norm_num)).2.2.2
  have m : B.Inside (13/10) (12/5) := by
    exact ⟨by nlinarith only [upperU,bc1,bs,ha],
      by nlinarith only [bottom.2.1,bc,bs],
      by linarith only [upperV,mSpan,ha],
      by nlinarith only [top.2.2.2,bc,bs]⟩
  have tangent := (short_projections B (25/27) (-(10/27)) (by norm_num)).2.1
  have steep : 7/20 < -B.s := by linarith only [height,ha,tangent]
  have narrow : B.c-(9/50)*B.s < 1 := by
    apply lt_of_not_ge
    intro large
    have square := mul_nonneg
      (by linarith only [large] : 0 ≤ B.c-(1+(9/50)*B.s))
      (by linarith only [bc,bs1] : 0 ≤ B.c+(1+(9/50)*B.s))
    have positive := mul_pos (by linarith only [steep] : 0 < -B.s)
      (by linarith only [steep] : 0 < -(2581/2500)*B.s-9/25)
    nlinarith only [square,positive,B.unit_normal]
  have sum : B.c-B.s ≤ 283/200 := by
    nlinarith [B.unit_normal,sq_nonneg (B.c+B.s)]
  have nVspan : -B.s+(203/500)*B.c < 1 := by linarith only [sum,bsc]
  have n : B.Inside 1 (67/25) := by
    simp only [OpenSquare.Inside,InBands,mul_one]
    exact ⟨by linarith only [upperU,narrow,ha],
      by nlinarith only [top.2.1,bc,bsc],
      by linarith only [upperV,nVspan,ha],
      by nlinarith only [top.2.2.2,bc,bs]⟩
  exact ⟨m,n⟩

end N12Compact.FourSquareBNegative

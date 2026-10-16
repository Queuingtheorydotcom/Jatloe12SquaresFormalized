import Compact.Completion.C981.WallScalars
import Compact.Geometry.ClosedFrames
import S12.Convex
import Mathlib.Tactic.LinearCombination

/-! Theorems 6--7 of C981-WALL-CYCLES. A central square with the true
inward and outward anchors must cross the whole foreign bottom segment.
No side cap, discretized orientation or favorable separation is assumed. -/
namespace N12Compact.C981CompletionOutwardAnchor

open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem strict_closed_segment (q : OpenSquare) (x y x' y' t : ℝ)
    (closed : ClosedInside q x y) (strict : q.Inside x' y')
    (positive : 0 < t) (small : t < 1) :
    q.Inside ((1-t)*x+t*x') ((1-t)*y+t*y') := by
  have first : 0 ≤ 1-t := by linarith only [small]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [mul_nonneg first (sub_nonneg.mpr closed.1),
      mul_pos positive (sub_pos.mpr strict.1)]
  · nlinarith only [mul_nonneg first (sub_nonneg.mpr closed.2.1),
      mul_pos positive (sub_pos.mpr strict.2.1)]
  · nlinarith only [mul_nonneg first (sub_nonneg.mpr closed.2.2.1),
      mul_pos positive (sub_pos.mpr strict.2.2.1)]
  · nlinarith only [mul_nonneg first (sub_nonneg.mpr closed.2.2.2),
      mul_pos positive (sub_pos.mpr strict.2.2.2)]

private theorem crossing (q : OpenSquare) (x y : ℝ)
    (closed : ClosedInside q x y)
    (xlow : 113/50 < x) (xhigh : x < 14/5) (ylow : y < 1)
    (marker : q.Inside (47/20) (33/20))
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬ q.Inside z 1) : False := by
  let t := (1-y)/(33/20-y)
  have denominator : 0 < 33/20-y := by linarith only [ylow]
  have positive : 0 < t := div_pos (by linarith only [ylow]) denominator
  have small : t < 1 := (div_lt_one denominator).mpr (by linarith)
  have relation : t*(33/20-y)=1-y := div_mul_cancel₀ _ denominator.ne'
  have identity : (1-t)*y+t*(33/20)=1 := by nlinarith only [relation]
  have lower : 113/50 ≤ (1-t)*x+t*(47/20) := by
    have weighted := mul_nonneg (show 0 ≤ 1-t by linarith only [small])
      (show 0 ≤ x-113/50 by linarith only [xlow])
    nlinarith only [weighted,positive.le]
  have upper : (1-t)*x+t*(47/20) ≤ 14/5 := by
    have weighted := mul_nonneg (show 0 ≤ 1-t by linarith only [small])
      (show 0 ≤ 14/5-x by linarith only [xhigh])
    nlinarith only [weighted,positive.le]
  have point := strict_closed_segment q x y (47/20) (33/20) t
    closed marker positive small
  rw [identity] at point
  exact avoid _ lower upper point

private theorem positive_impossible (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (33/20)) (outward : q.Inside 3 (8/5))
    (cornerMissing : ¬ q.Inside 3 1)
    (wallMissing : ¬ q.Inside (1543/500) 2)
    (inwardMissing : ¬ q.Inside (113/50) 2)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬ q.Inside z 1) : False := by
  classical
  have cone : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have pUlo : q.loU < 3*q.c+q.s := by linarith only [marker.1,order]
  have pUhi : 3*q.c+q.s < q.loU+q.side := by linarith only [outward.2.1,hs]
  have pVhi : -3*q.s+q.c < q.loV+q.side := by linarith only [outward.2.2.2,hc]
  have pFace : -3*q.s+q.c ≤ q.loV :=
    le_of_not_gt (fun v => cornerMissing
      ⟨by linarith only [pUlo],
        by linarith only [pUhi],
        by linarith only [v],
        by linarith only [pVhi]⟩)
  have rUlo : q.loU < (1543/500)*q.c+2*q.s := by
    linarith only [outward.1,hc,hs]
  have rVlo : q.loV < -(1543/500)*q.s+2*q.c := by
    linarith only [outward.2.2.1,hc,order]
  have rVhi : -(1543/500)*q.s+2*q.c < q.loV+q.side := by
    linarith only [pFace,side,cone,hs]
  have rFace : q.loU+q.side ≤ (1543/500)*q.c+2*q.s :=
    le_of_not_gt (fun u => wallMissing ⟨by linarith only [rUlo],by linarith only [u],by linarith only [rVlo],by linarith only [rVhi]⟩)
  have gUhi : (113/50)*q.c+2*q.s < q.loU+q.side := by
    linarith only [outward.2.1,hc,order]
  have gVlo : q.loV < -(113/50)*q.s+2*q.c := by
    linarith only [marker.2.2.1,hc,hs]
  have gUlo : q.loU < (113/50)*q.c+2*q.s := by
    linarith only [rFace,side,cone]
  have gFace : q.loV+q.side ≤ -(113/50)*q.s+2*q.c :=
    le_of_not_gt (fun v => inwardMissing ⟨by linarith only [gUlo],by linarith only [gUhi],by linarith only [gVlo],by linarith only [v]⟩)
  have fUhi : (113/50)*q.c+q.s < q.loU+q.side := by
    linarith only [outward.2.1,hc,hs]
  have fVhi : -(113/50)*q.s+q.c < q.loV+q.side := by
    linarith only [marker.2.2.2,hc,order]
  have fVlo : q.loV < -(113/50)*q.s+q.c := by
    linarith only [gFace,side,cone]
  have fFace : (113/50)*q.c+q.s ≤ q.loU :=
    le_of_not_gt (fun u => avoid (113/50) (by rfl) (by norm_num)
      ⟨by linarith only [u],
        by linarith only [fUhi],
        by linarith only [fVlo],
        by linarith only [fVhi]⟩)
  have tUhi : (14/5)*q.c+q.s < q.loU+q.side := by
    linarith only [outward.2.1,hc,hs]
  have tVhi : -(14/5)*q.s+q.c < q.loV+q.side := by
    linarith only [marker.2.2.2,hc,hs]
  have short := C981CompletionWallScalars.canonical_projection q.c q.s hc.le hs
    order q.unit_normal
  have tUlo : q.loU < (14/5)*q.c+q.s := by
    linarith only [rFace,short,side]
  have tFace : -(14/5)*q.s+q.c ≤ q.loV :=
    le_of_not_gt (fun v => avoid (14/5) (by norm_num) (by rfl)
      ⟨by linarith only [tUlo],
        by linarith only [tUhi],
        by linarith only [v],
        by linarith only [tVhi]⟩)
  have sine : 0 < q.s := by
    apply lt_of_not_ge
    intro nonpos
    have zero : q.s=0 := le_antisymm nonpos hs
    rw [zero] at gFace tFace
    linarith only [gFace,tFace,side,cone]
  let x := q.c*q.loU-q.s*q.loV
  let y := q.s*q.loU+q.c*q.loV
  have closed : ClosedInside q x y := by
    have u : q.c*x+q.s*y=q.loU := by
      dsimp [x,y]
      linear_combination q.loU*q.unit_normal
    have v : -q.s*x+q.c*y=q.loV := by
      dsimp [x,y]
      linear_combination q.loV*q.unit_normal
    dsimp [ClosedInside]
    rw [u,v]
    exact ⟨le_rfl,by linarith only [q.side_pos],le_rfl,by linarith only [q.side_pos]⟩
  have lowProduct := mul_nonneg hc.le (sub_nonneg.mpr fFace)
  have topProduct := mul_nonneg hs (sub_nonneg.mpr gFace)
  have long := mul_pos sine (show 0 < q.side-q.c by linarith only [side,cone])
  have xLow : 113/50 < x := by
    dsimp [x]
    nlinarith only [lowProduct,topProduct,long,q.unit_normal]
  have rightProduct := mul_nonneg hc.le (sub_nonneg.mpr rFace)
  have bottomProduct := mul_nonneg hs (sub_nonneg.mpr tFace)
  have width := mul_pos hc (sub_pos.mpr side)
  have shortProduct := mul_pos hc (show 0 < 1-((143/500)*q.c+q.s)
    by linarith only [short])
  have xHigh : x < 14/5 := by
    dsimp [x]
    nlinarith only [rightProduct,bottomProduct,width,shortProduct,q.unit_normal]
  have cross := mul_pos hc sine
  have sum : 1 ≤ q.c+q.s := by
    nlinarith only [q.unit_normal,cross,hc,hs]
  have sumHigh : q.c+q.s ≤ 99/70 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),hc,hs]
  have arc : 1+(413/500)*q.c*q.s < q.c+q.s := by
    have remainder := mul_nonneg (sub_nonneg.mpr sumHigh) (sub_nonneg.mpr sum)
    nlinarith only [remainder,q.unit_normal,cross]
  have rHeight := mul_nonneg hs (sub_nonneg.mpr rFace)
  have gHeight := mul_nonneg hc.le (sub_nonneg.mpr gFace)
  have tall := mul_pos (sub_pos.mpr side)
    (show 0 < q.c+q.s by linarith only [sum])
  have yLow : y < 1 := by
    dsimp [y]
    nlinarith only [rHeight,gHeight,tall,arc,q.unit_normal]
  exact crossing q x y closed xLow xHigh yLow marker avoid

/-- Canonical outward sign lock, independent of an inward anchor.
It rules out the entire nonnegative canonical sector, including both ends. -/
theorem nonnegative_impossible (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (47/20) (33/20)) (outward : q.Inside 3 (8/5))
    (cornerMissing : ¬ q.Inside 3 1)
    (wallMissing : ¬ q.Inside (1543/500) 2)
    (inwardMissing : ¬ q.Inside (113/50) 2)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬ q.Inside z 1) : False :=
  positive_impossible q side hc hs order marker outward cornerMissing
    wallMissing inwardMissing avoid

private theorem nonpositive_impossible (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (inward : q.Inside 2 (87/50)) (outward : q.Inside 3 (8/5))
    (inwardMissing : ¬ q.Inside (113/50) 2)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬ q.Inside z 1) : False := by
  classical
  have cone : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have gUlo : q.loU < (113/50)*q.c+2*q.s := by
    linarith only [inward.1,order]
  have gUhi : (113/50)*q.c+2*q.s < q.loU+q.side := by
    linarith only [outward.2.1,hc,hs]
  have gVlo : q.loV < -(113/50)*q.s+2*q.c := by
    linarith only [inward.2.2.1,hc,hs]
  have gFace : q.loV+q.side ≤ -(113/50)*q.s+2*q.c :=
    le_of_not_gt (fun v => inwardMissing ⟨by linarith only [gUlo],by linarith only [gUhi],by linarith only [gVlo],by linarith only [v]⟩)
  have fUlo : q.loU < (113/50)*q.c+q.s := by
    linarith only [inward.1,hc,hs]
  have fUhi : (113/50)*q.c+q.s < q.loU+q.side := by
    linarith only [outward.2.1,hc,order]
  have fVhi : -(113/50)*q.s+q.c < q.loV+q.side := by
    linarith only [inward.2.2.2,hc,order]
  have fFace : -(113/50)*q.s+q.c ≤ q.loV :=
    le_of_not_gt (fun v => avoid (113/50) (by rfl) (by norm_num)
      ⟨by linarith only [fUlo],
        by linarith only [fUhi],
        by linarith only [v],
        by linarith only [fVhi]⟩)
  linarith only [fFace,gFace,side,cone]

/-- Complete all-orientation obstruction for the exact original anchors.
The entire excluded segment, including its endpoints, is required. -/
theorem impossible (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (33/20))
    (inward : q.Inside 2 (87/50)) (outward : q.Inside 3 (8/5))
    (cornerMissing : ¬ q.Inside 3 1)
    (wallMissing : ¬ q.Inside (1543/500) 2)
    (inwardMissing : ¬ q.Inside (113/50) 2)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬ q.Inside z 1) : False := by
  obtain ⟨r,hc,order,shape,equivalent,_⟩ := ClosedFrames.canonical_frame q
  have rSide : 1 < r.side := by simpa only [shape] using side
  have rAvoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬ r.Inside z 1 := by
    intro z lo hi point
    exact avoid z lo hi ((equivalent _ _).mp point)
  by_cases positive : 0 ≤ r.s
  · exact positive_impossible r rSide hc positive
      (by simpa only [abs_of_nonneg positive] using order)
      ((equivalent _ _).mpr marker) ((equivalent _ _).mpr outward)
      (fun h => cornerMissing ((equivalent _ _).mp h))
      (fun h => wallMissing ((equivalent _ _).mp h))
      (fun h => inwardMissing ((equivalent _ _).mp h)) rAvoid
  · have negative : r.s ≤ 0 := le_of_lt (lt_of_not_ge positive)
    exact nonpositive_impossible r rSide hc negative
      (by simpa only [abs_of_nonpos negative] using order)
      ((equivalent _ _).mpr inward) ((equivalent _ _).mpr outward)
      (fun h => inwardMissing ((equivalent _ _).mp h)) rAvoid

#print axioms impossible
end N12Compact.C981CompletionOutwardAnchor

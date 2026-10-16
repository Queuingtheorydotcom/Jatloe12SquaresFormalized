import Compact.Geometry.ClosedPointExclusion
import S12.Symmetry

/-! Direct forced point for positive shallow A. This avoids deriving a long
section first. The two extra exclusions are consequences of actual foreign
closed compulsory points, not assumptions of strict ownership. -/

namespace N12Compact.FourSquareAForced

open S12 S12Pilot FourSquareAnchors

/-- The higher forced point and the original closed P vertex also force the
middle grid point on the packing cut, so B's radius-safe case is excluded. -/
theorem row_point (q : OpenSquare) (hP : ClosedInside q 2 (113/50))
    (high : q.Inside 2 (5/2)) : q.Inside 2 (12/5) := by
  exact ⟨by linarith only [hP.1,high.1],
    by linarith only [hP.2.1,high.2.1],
    by linarith only [hP.2.2.1,high.2.2.1],
    by linarith only [hP.2.2.2,high.2.2.2]⟩

theorem positive_wide_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 < q.s) (hangle : 20*q.s ≤ 99*q.c)
    (hP : ClosedInside q 2 (113/50))
    (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hG : ¬ q.Inside (47/20) (33/20))
    (hB : ¬ q.Inside (33/20) (47/20))
    (hR : ¬ q.Inside 3 (12/5)) : q.Inside 2 (5/2) := by
  have hcpos : 0 < q.c := by linarith only [hs,hangle]
  have hprojection : q.s + q.c/10 ≤ 1 := by
    nlinarith [q.unit_normal,mul_nonneg hc (sub_nonneg.mpr hangle)]
  have hspan : (7/10)*(q.c+q.s) ≤ 1 := by
    nlinarith [q.unit_normal, sq_nonneg (q.c-q.s)]
  have gUhi : q.c*(47/20)+q.s*(33/20) < q.loU+q.side := by linarith [hT.2.1]
  have gVhi : -q.s*(47/20)+q.c*(33/20) < q.loV+q.side := by linarith [hP.2.2.2]
  have modes : q.c*(47/20)+q.s*(33/20) ≤ q.loU ∨
      -q.s*(47/20)+q.c*(33/20) ≤ q.loV := by
    by_cases hu : q.c*(47/20)+q.s*(33/20) ≤ q.loU
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => hG ⟨lt_of_not_ge hu,gUhi,hv,gVhi⟩))
  have targetUlo : q.loU < q.c*2+q.s*(5/2) := by linarith [hP.1]
  have targetVlo : q.loV < -q.s*2+q.c*(5/2) := by linarith [hQ.2.2.1]
  have targetG := short_projections q (-7/20) (17/20) (by norm_num)
  rcases modes with huG | hvG
  · have angle : (7/20)*q.c ≤ (61/100)*q.s := by linarith [hP.1]
    have proj := (short_projections q (13/20) (3/4) (by norm_num)).2.1
    have rUlo : q.loU < q.c*3+q.s*(12/5) := by linarith [hT.1]
    have rUhi : q.c*3+q.s*(12/5) < q.loU+q.side := by linarith only [huG,proj,ha]
    have rVhi : -q.s*3+q.c*(12/5) < q.loV+q.side := by linarith [hP.2.2.2]
    have hvR : -q.s*3+q.c*(12/5) ≤ q.loV :=
      le_of_not_gt (fun h => hR ⟨rUlo,rUhi,h,rVhi⟩)
    exact ⟨targetUlo, by linarith only [huG,targetG.2.1,ha],
      targetVlo, by linarith only [hvR,hprojection,ha]⟩
  · have bUhi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by linarith [hT.2.1]
    have bVlo : q.loV < -q.s*(33/20)+q.c*(47/20) := by linarith [hQ.2.2.1]
    have bVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
      linarith only [hvG,hspan,ha]
    have huB : q.c*(33/20)+q.s*(47/20) ≤ q.loU :=
      le_of_not_gt (fun h => hB ⟨h,bUhi,bVlo,bVhi⟩)
    have targetB := (short_projections q (7/20) (3/20) (by norm_num)).2.1
    exact ⟨targetUlo, by linarith only [huB,targetB,ha],
      targetVlo, by linarith only [hvG,targetG.2.2.2,ha]⟩

theorem positive_shallow_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 < q.s) (hsc : q.s ≤ q.c)
    (hP : ClosedInside q 2 (113/50)) (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hG : ¬ q.Inside (47/20) (33/20))
    (hB : ¬ q.Inside (33/20) (47/20))
    (hR : ¬ q.Inside 3 (12/5)) : q.Inside 2 (5/2) :=
  positive_wide_point q ha hc hs (by linarith only [hsc,hc]) hP hQ hT hG hB hR

theorem of_foreign_closed (A B R : OpenSquare) (ha : 1 < A.side)
    (hc : 0 ≤ A.c) (hs : 0 < A.s) (hsc : A.s ≤ A.c)
    (hP : ClosedInside A 2 (113/50)) (hQ : ClosedInside A (113/50) 2)
    (hT : ClosedInside A (47/20) (47/20))
    (hG : ¬ A.Inside (47/20) (33/20))
    (b₀ : ClosedInside B (33/20) (47/20)) (r₀ : ClosedInside R 3 (12/5))
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 (5/2) :=
  positive_shallow_point A ha hc hs hsc hP hQ hT hG
    (ClosedPointExclusion.outside_of_closed A B _ _ ab b₀)
    (ClosedPointExclusion.outside_of_closed A R _ _ ar r₀)

theorem axis_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : q.c = 1) (hs : q.s = 0)
    (hP : ClosedInside q 2 (113/50)) (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hF : ¬ q.Inside (33/20) (33/20))
    (hG : ¬ q.Inside (47/20) (33/20))
    (hR : ¬ q.Inside 3 (12/5)) : q.Inside 2 (5/2) := by
  simp only [ClosedInside,hc,hs,zero_mul,one_mul,neg_zero,zero_add,add_zero] at hP hQ hT
  have hv : 33/20 ≤ q.loV := by
    apply le_of_not_gt
    intro low
    have high : 33/20 < q.loV+q.side := by linarith [hT.2.2.2]
    have uhi : q.loU+q.side ≤ 47/20 := by
      apply le_of_not_gt
      intro wide
      apply hG
      simp only [OpenSquare.Inside,InBands,hc,hs,zero_mul,one_mul,neg_zero,zero_add,add_zero]
      exact ⟨by linarith [hP.1],wide,low,high⟩
    apply hF
    simp only [OpenSquare.Inside,InBands,hc,hs,zero_mul,one_mul,neg_zero,zero_add,add_zero]
    exact ⟨by linarith only [uhi,ha],by linarith [hT.2.1],low,high⟩
  have rU : q.loU+q.side ≤ 3 := by
    apply le_of_not_gt
    intro wide
    apply hR
    simp only [OpenSquare.Inside,InBands,hc,hs,zero_mul,one_mul,neg_zero,zero_add,add_zero]
    exact ⟨by linarith [hP.1],wide,by linarith [hQ.2.2.1],by linarith only [hv,ha]⟩
  simp only [OpenSquare.Inside,InBands,hc,hs,zero_mul,one_mul,neg_zero,zero_add,add_zero]
  exact ⟨by linarith only [rU,ha],by linarith [hQ.2.1],
    by linarith [hQ.2.2.1],by linarith only [hv,ha]⟩

/-- The positive shallow orientation sector includes both angle endpoints.
No upper side cap or container bound is required for this forced point. -/
theorem wide_with_axis (A B R : OpenSquare) (ha : 1 < A.side)
    (hc : 0 ≤ A.c) (hs : 0 ≤ A.s) (hangle : 20*A.s ≤ 99*A.c)
    (hP : ClosedInside A 2 (113/50)) (hQ : ClosedInside A (113/50) 2)
    (hT : ClosedInside A (47/20) (47/20))
    (hF : ¬ A.Inside (33/20) (33/20)) (hG : ¬ A.Inside (47/20) (33/20))
    (b₀ : ClosedInside B (33/20) (47/20)) (r₀ : ClosedInside R 3 (12/5))
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 (5/2) := by
  by_cases zero : A.s = 0
  · have cOne : A.c = 1 := by nlinarith [A.unit_normal]
    exact axis_point A ha cOne zero hP hQ hT hF hG
      (ClosedPointExclusion.outside_of_closed A R _ _ ar r₀)
  · exact positive_wide_point A ha hc (lt_of_le_of_ne hs (Ne.symm zero)) hangle
      hP hQ hT hG
      (ClosedPointExclusion.outside_of_closed A B _ _ ab b₀)
      (ClosedPointExclusion.outside_of_closed A R _ _ ar r₀)

theorem shallow_with_axis (A B R : OpenSquare) (ha : 1 < A.side)
    (hc : 0 ≤ A.c) (hs : 0 ≤ A.s) (hsc : A.s ≤ A.c)
    (hP : ClosedInside A 2 (113/50)) (hQ : ClosedInside A (113/50) 2)
    (hT : ClosedInside A (47/20) (47/20))
    (hF : ¬ A.Inside (33/20) (33/20)) (hG : ¬ A.Inside (47/20) (33/20))
    (b₀ : ClosedInside B (33/20) (47/20)) (r₀ : ClosedInside R 3 (12/5))
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) : A.Inside 2 (5/2) :=
  wide_with_axis A B R ha hc hs (by linarith only [hsc,hc])
    hP hQ hT hF hG b₀ r₀ ab ar

end N12Compact.FourSquareAForced

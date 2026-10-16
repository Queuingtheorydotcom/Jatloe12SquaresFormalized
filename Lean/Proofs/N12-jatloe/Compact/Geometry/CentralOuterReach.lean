import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The complete elbow square reaches both outer arms. The two foreign
outer points are essential: one selects the upper transverse face in the
otherwise unresolved lower-face branch. No side cap or enclosure is used. -/
namespace N12Compact.CentralOuterReach
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (p : q.Inside 2 (113/50)) (r : q.Inside (113/50) 2)
    (t : q.Inside (47/20) (47/20))
    (missingG : ¬ q.Inside (47/20) (33/20))
    (missingB : ¬ q.Inside (33/20) (47/20))
    (missingR : ¬ q.Inside 3 (12/5))
    (missingTop : ¬ q.Inside (12/5) 3)
    (x y : ℝ) (hx : 47/20 ≤ x) (hy : 47/20 ≤ y)
    (slope : x-47/20 ≤ y-33/20)
    (gShort : (x-47/20)^2+(y-33/20)^2 ≤ 1)
    (bShort : (x-33/20)^2+(y-47/20)^2 ≤ 1)
    (rShort : (x-3)^2+(y-12/5)^2 ≤ 1)
    (topShort : (x-12/5)^2+(y-3)^2 ≤ 1) : q.Inside x y := by
  have targetUlo : q.loU < q.c*x+q.s*y := by
    have dx := mul_nonneg hc.le (sub_nonneg.mpr hx)
    have dy := mul_nonneg hs (sub_nonneg.mpr hy)
    nlinarith only [t.1,dx,dy]
  have fromG := short_projections q (x-47/20) (y-33/20) gShort
  have fromB := short_projections q (x-33/20) (y-47/20) bShort
  have fromR := short_projections q (x-3) (y-12/5) rShort
  have fromTop := short_projections q (x-12/5) (y-3) topShort
  by_cases gv : -q.s*(47/20)+q.c*(33/20) ≤ q.loV
  · have span : (7/10)*(q.c+q.s) ≤ 1 := by
      nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),
        sq_nonneg ((7/10)*(q.c+q.s)-1)]
    have bUhi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by
      linarith only [t.2.1,hc]
    have bVlo : q.loV < -q.s*(33/20)+q.c*(47/20) := by
      linarith only [r.2.2.1,hc,hs]
    have bVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
      linarith only [gv,span,ha]
    have bu : q.c*(33/20)+q.s*(47/20) ≤ q.loU :=
      le_of_not_gt (fun h => missingB ⟨h,bUhi,bVlo,bVhi⟩)
    have topUlo : q.loU < q.c*(12/5)+q.s*3 := by
      linarith only [t.1,hc,hs]
    have topVlo : q.loV < -q.s*(12/5)+q.c*3 := by
      linarith only [r.2.2.1,hc,hs,order]
    have gap := (short_projections q (3/4) (13/20) (by norm_num)).2.1
    have topUhi : q.c*(12/5)+q.s*3 < q.loU+q.side := by
      linarith only [bu,gap,ha]
    have topV : q.loV+q.side ≤ -q.s*(12/5)+q.c*3 :=
      le_of_not_gt (fun h => missingTop ⟨topUlo,topUhi,topVlo,h⟩)
    exact ⟨targetUlo,by nlinarith only [bu,fromB.2.1,ha],
      by nlinarith only [topV,fromTop.2.2.1,ha],
      by nlinarith only [gv,fromG.2.2.2,ha]⟩
  · have gVlo := lt_of_not_ge gv
    have gUhi : q.c*(47/20)+q.s*(33/20) < q.loU+q.side := by
      linarith only [t.2.1,hs]
    have gVhi : -q.s*(47/20)+q.c*(33/20) < q.loV+q.side := by
      linarith only [p.2.2.2,hc,hs]
    have gu : q.c*(47/20)+q.s*(33/20) ≤ q.loU :=
      le_of_not_gt (fun h => missingG ⟨h,gUhi,gVlo,gVhi⟩)
    have angle : 35*q.c ≤ 61*q.s := by linarith only [gu,p.1]
    have gap := (short_projections q (13/20) (3/4) (by norm_num)).2.1
    have rUlo : q.loU < q.c*3+q.s*(12/5) := by
      linarith only [t.1,hc,hs]
    have rUhi : q.c*3+q.s*(12/5) < q.loU+q.side := by
      linarith only [gu,gap,ha]
    have rVhi : -q.s*3+q.c*(12/5) < q.loV+q.side := by
      linarith only [p.2.2.2,angle,hc]
    have rv : -q.s*3+q.c*(12/5) ≤ q.loV :=
      le_of_not_gt (fun h => missingR ⟨rUlo,rUhi,h,rVhi⟩)
    have targetVlo : q.loV < -q.s*x+q.c*y := by
      have first := mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr hx)
      have second := mul_nonneg hc.le (sub_nonneg.mpr slope)
      nlinarith only [gVlo,first,second]
    exact ⟨targetUlo,by nlinarith only [gu,fromG.2.1,ha],targetVlo,
      by nlinarith only [rv,fromR.2.2.2,ha]⟩

private theorem positive_points (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (p : q.Inside 2 (113/50)) (r : q.Inside (113/50) 2)
    (t : q.Inside (47/20) (47/20))
    (missingG : ¬ q.Inside (47/20) (33/20))
    (missingB : ¬ q.Inside (33/20) (47/20))
    (missingR : ¬ q.Inside 3 (12/5))
    (missingTop : ¬ q.Inside (12/5) 3) :
    q.Inside (47/20) (53/20) ∧ q.Inside (53/20) (47/20) := by
  constructor
  · exact positive_point q ha hc hs order p r t missingG missingB missingR
      missingTop _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact positive_point q ha hc hs order p r t missingG missingB missingR
      missingTop _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Both outward arms of the actual elbow square, for every orientation.
The strict side inequality handles the unit-length limiting vectors. -/
theorem points (q : OpenSquare) (ha : 1 < q.side)
    (p : q.Inside 2 (113/50)) (r : q.Inside (113/50) 2)
    (t : q.Inside (47/20) (47/20))
    (missingG : ¬ q.Inside (47/20) (33/20))
    (missingB : ¬ q.Inside (33/20) (47/20))
    (missingR : ¬ q.Inside 3 (12/5))
    (missingTop : ¬ q.Inside (12/5) 3) :
    q.Inside (47/20) (53/20) ∧ q.Inside (53/20) (47/20) := by
  obtain ⟨a,hc,hs,side,inside,_⟩ := ClosedFrames.positive_frame q
  have ha' : 1 < a.side := by simpa only [side] using ha
  have p' := (inside _ _).mpr p
  have r' := (inside _ _).mpr r
  have t' := (inside _ _).mpr t
  have g' : ¬ a.Inside (47/20) (33/20) := fun h => missingG ((inside _ _).mp h)
  have b' : ¬ a.Inside (33/20) (47/20) := fun h => missingB ((inside _ _).mp h)
  have right' : ¬ a.Inside 3 (12/5) := fun h => missingR ((inside _ _).mp h)
  have top' : ¬ a.Inside (12/5) 3 := fun h => missingTop ((inside _ _).mp h)
  by_cases order : a.s ≤ a.c
  · have h := positive_points a ha' hc hs order p' r' t' g' b' right' top'
    exact ⟨(inside _ _).mp h.1,(inside _ _).mp h.2⟩
  · have h := positive_points (pullSwap a) ha'
      (by dsimp [pullSwap]; linarith only [hc,lt_of_not_ge order]) hc.le
      (by dsimp [pullSwap]; exact (lt_of_not_ge order).le)
      ((inside_pullSwap a _ _).mpr r') ((inside_pullSwap a _ _).mpr p')
      ((inside_pullSwap a _ _).mpr t')
      (fun h => b' ((inside_pullSwap a _ _).mp h))
      (fun h => g' ((inside_pullSwap a _ _).mp h))
      (fun h => top' ((inside_pullSwap a _ _).mp h))
      (fun h => right' ((inside_pullSwap a _ _).mp h))
    exact ⟨(inside _ _).mp ((inside_pullSwap a _ _).mp h.2),
      (inside _ _).mp ((inside_pullSwap a _ _).mp h.1)⟩

#print axioms points
end N12Compact.CentralOuterReach

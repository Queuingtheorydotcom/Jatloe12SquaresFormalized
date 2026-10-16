import S12.ShortCluster
import S12.WallGeometry

/-! A wall owner's inward auxiliary conflicts with its genuine lower
singleton point. The argument has no angle mesh, containment premise,
side cap or assumed sign. Reindexing preserves the physical square. -/
namespace N12Compact.C981InwardWall

open S12 S12Pilot
set_option Elab.async false

private theorem span_lt_one (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) (slope : 37*s ≤ 13*c) :
    (89/100)*c+(12/25)*s < 1 := by
  have half : 2*s ≤ c := by linarith only [slope,hc]
  have factor : 0 ≤ 243107*c-318901*s := by linarith only [half,hc]
  have product := mul_nonneg
    (show 0 ≤ 13*c-37*s by linarith only [slope]) factor
  have identity :
      3917^2*(c^2+s^2)-1538*(89*c+48*s)^2 =
        (13*c-37*s)*(243107*c-318901*s) := by ring
  rw [unit] at identity
  by_contra failed
  have large : 100 ≤ 89*c+48*s := by linarith only [failed]
  have square := mul_nonneg (sub_nonneg.mpr large)
    (show 0 ≤ 89*c+48*s+100 by linarith only [hc,hs])
  nlinarith only [identity,product,square]

private theorem positive_impossible (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : q.Inside (457/500) 2) (upper : q.Inside 1 (12/5))
    (inward : q.Inside (87/50) 2)
    (lowerMissing : ¬ q.Inside 1 (87/50))
    (markerMissing : ¬ q.Inside (33/20) (47/20))
    (singletonMissing : ¬ q.Inside (19/25) (187/100)) : False := by
  have nUlo : q.loU < q.c*(33/20)+q.s*(47/20) := by
    linarith only [wall.1,hc,hs]
  have nVlo : q.loV < -q.s*(33/20)+q.c*(47/20) := by
    linarith only [inward.2.2.1,hc,hs]
  have nVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
    linarith only [upper.2.2.2,hc,hs]
  have nFace : q.loU+q.side ≤ q.c*(33/20)+q.s*(47/20) :=
    le_of_not_gt (fun h => markerMissing ⟨nUlo,h,nVlo,nVhi⟩)
  have slopeLow : 9*q.c < 35*q.s := by
    linarith only [nFace,inward.2.1]
  have fUhi : q.c+q.s*(87/50) < q.loU+q.side := by
    linarith only [inward.2.1,hc,hs]
  have fVhi : -q.s+q.c*(87/50) < q.loV+q.side := by
    linarith only [upper.2.2.2,hc]
  have fModes : q.c+q.s*(87/50) ≤ q.loU ∨
      -q.s+q.c*(87/50) ≤ q.loV := by
    by_cases low : q.c+q.s*(87/50) ≤ q.loU
    · exact Or.inl low
    · exact Or.inr (le_of_not_gt (fun h => lowerMissing
        ⟨by simpa only [mul_one] using lt_of_not_ge low,
          by simpa only [mul_one] using fUhi,
          by simpa only [mul_one] using h,
          by simpa only [mul_one] using fVhi⟩))
  have fFace : -q.s+q.c*(87/50) ≤ q.loV := by
    rcases fModes with u | v
    · have short := (short_projections q (13/20) (61/100) (by norm_num)).2.1
      linarith only [u,nFace,short,side]
    · exact v
  have slopeHigh : 37*q.s < 13*q.c := by
    linarith only [fFace,inward.2.2.1]
  have hUhi : q.c*(19/25)+q.s*(187/100) < q.loU+q.side := by
    linarith only [wall.2.1,hc,hs]
  have hVlo : q.loV < -q.s*(19/25)+q.c*(187/100) := by
    linarith only [inward.2.2.1,slopeLow,hc,hs]
  have hVhi : -q.s*(19/25)+q.c*(187/100) < q.loV+q.side := by
    linarith only [upper.2.2.2,slopeHigh,hc,hs]
  have hFace : q.c*(19/25)+q.s*(187/100) ≤ q.loU :=
    le_of_not_gt (fun h => singletonMissing ⟨h,hUhi,hVlo,hVhi⟩)
  have span := span_lt_one q.c q.s hc hs q.unit_normal slopeHigh.le
  linarith only [hFace,nFace,span,side]

/-- All orientations and every possible equality at a missing point are
retained. The singleton point must be supplied by its genuine owner. -/
theorem impossible (q : OpenSquare) (side : 1 < q.side)
    (wall : q.Inside (457/500) 2) (upper : q.Inside 1 (12/5))
    (inward : q.Inside (87/50) 2)
    (lowerMissing : ¬ q.Inside 1 (87/50))
    (markerMissing : ¬ q.Inside (33/20) (47/20))
    (singletonMissing : ¬ q.Inside (19/25) (187/100)) : False := by
  obtain ⟨r,hc,hs,shape,_,_,equivalent⟩ := exists_positive_frame q
  exact positive_impossible r (by simpa only [shape] using side) hc hs
    ((equivalent _ _).mpr wall) ((equivalent _ _).mpr upper)
    ((equivalent _ _).mpr inward)
    (fun h => lowerMissing ((equivalent _ _).mp h))
    (fun h => markerMissing ((equivalent _ _).mp h))
    (fun h => singletonMissing ((equivalent _ _).mp h))

#print axioms impossible
end N12Compact.C981InwardWall

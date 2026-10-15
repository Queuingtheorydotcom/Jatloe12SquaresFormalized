import Compact.Geometry.FourSquareAForced

/-! Completes the final A orientation interval once the actual right-wall
neighbor has been shown to contain (3,5/2). All positive frames are covered,
including the axis and both sides of the rational angle split. -/

namespace N12Compact.FourSquareANarrow

open S12 S12Pilot FourSquareAnchors

theorem point_of_higher_R (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s)
    (hP : ClosedInside q 2 (113/50)) (hQ : ClosedInside q (113/50) 2)
    (hT : ClosedInside q (47/20) (47/20))
    (hF : ¬ q.Inside (33/20) (33/20))
    (hG : ¬ q.Inside (47/20) (33/20))
    (hB : ¬ q.Inside (33/20) (47/20))
    (hR : ¬ q.Inside 3 (12/5))
    (hRhigh : ¬ q.Inside 3 (5/2)) : q.Inside 2 (5/2) := by
  by_cases zero : q.s = 0
  · have cOne : q.c = 1 := by nlinarith [q.unit_normal]
    exact FourSquareAForced.axis_point q ha cOne zero hP hQ hT hF hG hR
  have spos : 0 < q.s := lt_of_le_of_ne hs (Ne.symm zero)
  by_cases wide : 20*q.s ≤ 99*q.c
  · exact FourSquareAForced.positive_wide_point q ha hc.le spos wide hP hQ hT hG hB hR
  have narrow : 99*q.c < 20*q.s := lt_of_not_ge wide
  have hs1 : q.s ≤ 1 := by nlinarith [q.unit_normal,sq_nonneg q.c]
  have span : (7/10)*(q.c+q.s) ≤ 1 := by nlinarith [q.unit_normal,sq_nonneg (q.c-q.s)]
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
  rcases modes with gu | gv
  · have rUlo : q.loU < q.c*3+q.s*(5/2) := by linarith [hT.1]
    have rUhi : q.c*3+q.s*(5/2) < q.loU+q.side := by
      linarith only [gu,narrow,hs1,ha]
    have rVhi : -q.s*3+q.c*(5/2) < q.loV+q.side := by
      linarith [hP.2.2.2]
    have rv : -q.s*3+q.c*(5/2) ≤ q.loV :=
      le_of_not_gt (fun h => hRhigh ⟨rUlo,rUhi,h,rVhi⟩)
    exact ⟨targetUlo,by linarith only [gu,targetG.2.1,ha],
      targetVlo,by linarith only [rv,hs1,ha]⟩
  · have bUhi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by linarith [hT.2.1]
    have bVlo : q.loV < -q.s*(33/20)+q.c*(47/20) := by linarith [hQ.2.2.1]
    have bVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
      linarith only [gv,span,ha]
    have bu : q.c*(33/20)+q.s*(47/20) ≤ q.loU :=
      le_of_not_gt (fun h => hB ⟨h,bUhi,bVlo,bVhi⟩)
    have targetB := (short_projections q (7/20) (3/20) (by norm_num)).2.1
    exact ⟨targetUlo,by linarith only [bu,targetB,ha],
      targetVlo,by linarith only [gv,targetG.2.2.2,ha]⟩

end N12Compact.FourSquareANarrow

import Compact.Geometry.WallLowerCenterBarrier

/-! A lower missing wall point and an upper missing central marker force
the point (1,2.56). No orientation, side cap, or enclosure is assumed. -/
namespace N12Compact.WallUpperMissingReach
open S12 S12Pilot
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side))
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hT : ¬ q.Inside (33/20) (47/20)) : q.Inside 1 (64/25) := by
  have hcs : 0 ≤ q.c*q.s := mul_nonneg hc hs
  have hsum : 1 ≤ q.c+q.s := by
    nlinarith only [q.unit_normal, hcs, hc, hs]
  have hsumhi : q.c+q.s ≤ 10/7 := by
    nlinarith only [q.unit_normal, sq_nonneg (q.c-q.s), hc, hs]
  have hsumstrong : 1+(41/50)*q.c*q.s ≤ q.c+q.s := by
    nlinarith only [q.unit_normal, hcs,
      mul_nonneg (sub_nonneg.mpr hsumhi) (sub_nonneg.mpr hsum)]
  have targetUlo : q.loU < q.c+q.s*(64/25) := by
    nlinarith only [hP.1, hc, hs]
  have targetVlo : q.loV < -q.s+q.c*(64/25) := by
    nlinarith only [hQ.2.2.1, hc]
  have wUhi : q.c+q.s*(87/50) < q.loU+q.side := by
    nlinarith only [hQ.2.1, hs]
  have wVhi : -q.s+q.c*(87/50) < q.loV+q.side := by
    nlinarith only [hP.2.2.2, hc, hs]
  have wmodes : q.c+q.s*(87/50) ≤ q.loU ∨
      -q.s+q.c*(87/50) ≤ q.loV := by
    by_cases hu : q.c+q.s*(87/50) ≤ q.loU
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv =>
        hW ⟨by simpa only [mul_one] using lt_of_not_ge hu,
          by simpa only [mul_one] using wUhi,
          by simpa only [mul_one] using hv,
          by simpa only [mul_one] using wVhi⟩))
  have targetW := short_projections q 0 (41/50) (by norm_num)
  simp only [OpenSquare.Inside, InBands, mul_one]
  rcases wmodes with wu | wv
  · have gap := (short_projections q (13/20) (61/100) (by norm_num)).2.1
    have tUlo : q.loU < q.c*(33/20)+q.s*(47/20) := by
      nlinarith only [hP.1, hc, hs]
    have tVhi : -q.s*(33/20)+q.c*(47/20) < q.loV+q.side := by
      nlinarith only [hQ.2.2.2, hc, hs]
    have tUhi : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by
      apply lt_of_not_ge
      intro upper
      linarith only [wu, upper, gap, ha]
    have tv : -q.s*(33/20)+q.c*(47/20) ≤ q.loV :=
      le_of_not_gt (fun lower => hT ⟨tUlo,tUhi,lower,tVhi⟩)
    have targetT := (short_projections q (-13/20) (21/100) (by norm_num)).2.2.2
    exact ⟨targetUlo,by linarith only [wu,targetW.2.1,ha],
      targetVlo,by linarith only [tv,targetT,ha]⟩
  · have vwall := mul_nonneg hs (sub_nonneg.mpr wv)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < q.c+q.s by linarith only [hsum])
    have targetUhi : q.c+q.s*(64/25) < q.loU+q.side := by
      apply lt_of_not_ge
      intro above
      have product := mul_nonneg hc (sub_nonneg.mpr above)
      nlinarith only [wall,vwall,strict,product,hsumstrong,q.unit_normal]
    exact ⟨targetUlo,targetUhi,targetVlo,by linarith only [wv,targetW.2.2.2,ha]⟩

/-- Reindexing preserves all four actual points and the complete square. -/
theorem point (q : OpenSquare) (ha : 1 < q.side) (box : InsideContainer q)
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hT : ¬ q.Inside (33/20) (47/20)) : q.Inside 1 (64/25) := by
  obtain ⟨r,hc,hs,hside,_,_,hi⟩ := exists_positive_frame q
  have rbox : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hp
    have hb := box x y ((hi x y).mp hp)
    exact ⟨hb.1,hb.2.2.1⟩
  have wall : 0 ≤ r.c*r.loU-r.s*(r.loV+r.side) := by
    have hx := (positive_frame_wall_bounds r hc hs rbox).1
    dsimp [centerX] at hx
    nlinarith only [hx]
  exact (hi _ _).mp (positive_point r (by simpa only [hside] using ha)
    hc hs wall ((hi _ _).mpr hP) ((hi _ _).mpr hQ)
    (fun hp => hW ((hi _ _).mp hp)) (fun hp => hT ((hi _ _).mp hp)))

#print axioms point
end N12Compact.WallUpperMissingReach

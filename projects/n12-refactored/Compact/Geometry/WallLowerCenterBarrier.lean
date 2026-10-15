import Compact.Geometry.WallCenterBarrier

/-! A lower foreign point on the wall row gives a quantitative center cut.
The entire orientation circle, including axis directions and square-boundary
contact, is covered by face reindexing. No side cap or enclosure is used. -/
namespace N12Compact.WallLowerCenterBarrier
open S12 S12Pilot
set_option Elab.async false

private theorem positive_center (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side))
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hT : ¬ q.Inside (33/20) (47/20)) : 21/10 < centerY q := by
  have hc1 : q.c ≤ 1 := by
    nlinarith only [q.unit_normal, sq_nonneg q.s, sq_nonneg (q.c-1)]
  have hcs : 0 ≤ q.c*q.s := mul_nonneg hc hs
  have hsum : 1 ≤ q.c+q.s := by
    nlinarith only [q.unit_normal, hcs, hc, hs]
  have hsumhi : q.c+q.s ≤ 3/2 := by
    nlinarith only [q.unit_normal, sq_nonneg (q.c-q.s), hc, hs]
  have hsumstrong : 1+(4/5)*q.c*q.s ≤ q.c+q.s := by
    nlinarith only [q.unit_normal,
      mul_nonneg (sub_nonneg.mpr hsumhi) (sub_nonneg.mpr hsum)]
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
    have uweight := mul_nonneg hs (sub_nonneg.mpr wu)
    have vweight := mul_nonneg hc (sub_nonneg.mpr tv)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < q.c+q.s by linarith only [hsum])
    have ss : q.s^2 ≤ 1 := by
      nlinarith only [q.unit_normal, sq_nonneg q.c]
    have cs : q.c*q.s ≤ 1/2 := by
      nlinarith only [q.unit_normal, sq_nonneg (q.c-q.s)]
    dsimp [centerY]
    nlinarith only [uweight, vweight, strict, q.unit_normal, hsumstrong, ss, cs]
  · have wweight := mul_nonneg hs wall
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < 1+q.s^2+q.c*q.s by
        nlinarith only [sq_nonneg q.s, hcs])
    have identity : q.c*centerY q =
        q.s*(q.c*q.loU-q.s*(q.loV+q.side)) + q.loV +
          q.side/2*(1+q.s^2+q.c*q.s) := by
      dsimp [centerY]
      calc
        _ = q.s*(q.c*q.loU-q.s*(q.loV+q.side)) +
            (q.c^2+q.s^2)*q.loV +
            q.side/2*((q.c^2+q.s^2)+q.s^2+q.c*q.s) := by ring
        _ = _ := by rw [q.unit_normal]; ring
    have margin : 0 ≤ (1+q.s^2+q.c*q.s)/2-q.s-(9/25)*q.c := by
      by_cases small : q.s ≤ 18/25
      · have product := mul_nonneg (sub_nonneg.mpr hc1)
          (show 0 ≤ 9/25-q.s/2 by linarith only [small])
        nlinarith only [product, sq_nonneg (q.s-1/2)]
      · have product := mul_nonneg hc
          (show 0 ≤ q.s/2-9/25 by linarith only [lt_of_not_ge small])
        nlinarith only [product, sq_nonneg (q.s-1)]
    have high : 0 < q.c*(centerY q-21/10) := by
      nlinarith only [identity, wweight, wv, strict, margin]
    apply lt_of_not_ge
    intro low
    exact (not_lt_of_ge
      (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr low))) high

/-- A lower missing wall point and an upper missing central point force the
original center above 2.1.
The four point premises refer to strict interiors; missing points may lie
on the boundary. Strictness of the conclusion comes from `side > 1`. -/
theorem center_above (q : OpenSquare) (ha : 1 < q.side) (box : InsideContainer q)
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hT : ¬ q.Inside (33/20) (47/20)) : 21/10 < centerY q := by
  obtain ⟨r,hc,hs,hside,_,hcy,hi⟩ := exists_positive_frame q
  have rbox : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hp
    have hb := box x y ((hi x y).mp hp)
    exact ⟨hb.1,hb.2.2.1⟩
  have wall : 0 ≤ r.c*r.loU-r.s*(r.loV+r.side) := by
    have hx := (positive_frame_wall_bounds r hc hs rbox).1
    dsimp [centerX] at hx
    nlinarith only [hx]
  have high := positive_center r (by simpa only [hside] using ha) hc hs wall
    ((hi _ _).mpr hP) ((hi _ _).mpr hQ)
    (fun hp => hW ((hi _ _).mp hp)) (fun hp => hT ((hi _ _).mp hp))
  simpa only [hcy] using high

#print axioms center_above
end N12Compact.WallLowerCenterBarrier

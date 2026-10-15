import Compact.Geometry.WallForcedPoint

/-! The wall point theorem with a lower point on the same vertical line.
This replaces a corner barrier by the actual foreign point (1,87/50).
Every inequality holds for the entire positive frame, including s = 0. -/
namespace N12Compact.WallLowerBarrier

open S12 S12Pilot FourSquareAnchors

theorem left_positive_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s)
    (wall : 0 ≤ q.c*q.loU - q.s*(q.loV+q.side))
    (hP : ClosedInside q (457/500) 2)
    (hQ : ClosedInside q 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hD : ¬ q.Inside (87/50) 2) : q.Inside 1 (5/2) := by
  simp only [OpenSquare.Inside, InBands, mul_one]
  have hsum : 1 ≤ q.c+q.s := by
    nlinarith [q.unit_normal, mul_nonneg hc.le hs]
  have hsumhi : q.c+q.s ≤ 3/2 := by
    nlinarith [q.unit_normal, sq_nonneg (q.c-q.s)]
  have hsumstrong : 1+(4/5)*q.c*q.s ≤ q.c+q.s := by
    nlinarith [q.unit_normal,
      mul_nonneg (sub_nonneg.mpr hsumhi) (sub_nonneg.mpr hsum)]
  have targetUlo : q.loU < q.c+q.s*(5/2) := by linarith [hP.1]
  have targetVlo : q.loV < -q.s+q.c*(5/2) := by linarith [hQ.2.2.1]
  have dUlo : q.loU < q.c*(87/50)+q.s*2 := by linarith [hP.1]
  have dVhi : -q.s*(87/50)+q.c*2 < q.loV+q.side := by
    linarith [hQ.2.2.2]
  have dmodes : q.loU+q.side ≤ q.c*(87/50)+q.s*2 ∨
      -q.s*(87/50)+q.c*2 ≤ q.loV := by
    by_cases hu : q.loU+q.side ≤ q.c*(87/50)+q.s*2
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv =>
        hD ⟨dUlo, lt_of_not_ge hu, hv, dVhi⟩))
  have wUhi : q.c+q.s*(87/50) < q.loU+q.side := by
    by_contra above
    have upper := le_of_not_gt above
    have hs0 : q.s = 0 := by linarith [hQ.2.1]
    have hc1 : q.c = 1 := by nlinarith [q.unit_normal]
    have wall0 : 0 ≤ q.loU := by simpa [hs0, hc1] using wall
    simp only [hs0, hc1, zero_mul, add_zero] at upper
    linarith only [upper, wall0, ha]
  have wVhi : -q.s+q.c*(87/50) < q.loV+q.side := by
    linarith [hP.2.2.2]
  have wmodes : q.c+q.s*(87/50) ≤ q.loU ∨
      -q.s+q.c*(87/50) ≤ q.loV := by
    by_cases hu : q.c+q.s*(87/50) ≤ q.loU
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv =>
        hW ⟨by simpa only [mul_one] using lt_of_not_ge hu,
          by simpa only [mul_one] using wUhi,
          by simpa only [mul_one] using hv,
          by simpa only [mul_one] using wVhi⟩))
  have targetW := short_projections q 0 (19/25) (by norm_num)
  rcases wmodes with wu | wv
  · have gap := (short_projections q (37/50) (13/50) (by norm_num)).2.1
    have dv : -q.s*(87/50)+q.c*2 ≤ q.loV := by
      rcases dmodes with du | dv
      · exfalso
        linarith only [wu, du, gap, ha]
      · exact dv
    have targetD := (short_projections q (-37/50) (1/2) (by norm_num)).2.2.2
    exact ⟨targetUlo, by linarith only [wu, targetW.2.1, ha],
      targetVlo, by linarith only [dv, targetD, ha]⟩
  · have vwall := mul_nonneg hs (sub_nonneg.mpr wv)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < q.c+q.s by linarith only [hc, hs])
    have targetUhi : q.c+q.s*(5/2) < q.loU+q.side := by
      apply lt_of_not_ge
      intro above
      have product := mul_nonneg hc.le (sub_nonneg.mpr above)
      nlinarith only [wall, vwall, strict, product, hsumstrong,
        q.unit_normal, mul_nonneg hc.le hs]
    exact ⟨targetUlo, targetUhi, targetVlo,
      by linarith only [wv, targetW.2.2.2, ha]⟩

#print axioms left_positive_point
end N12Compact.WallLowerBarrier

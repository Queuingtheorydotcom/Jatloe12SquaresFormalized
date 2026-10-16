import Compact.Geometry.WallLowerBarrier
import Compact.Geometry.WallCenterBarrier

/-! A wall square reaches height 2.56 uniformly in its orientation.
The point assumptions are actual strict ownership and actual exclusions.
The proof uses two possible escape faces, rather than angle intervals. -/
namespace N12Compact.WallLowerReach
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : 0 ≤ q.c*q.loU - q.s*(q.loV+q.side))
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hD : ¬ q.Inside (87/50) 2) : q.Inside 1 (64/25) := by
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
  have dUlo : q.loU < q.c*(87/50)+q.s*2 := by
    nlinarith only [hP.1, hc]
  have dVhi : -q.s*(87/50)+q.c*2 < q.loV+q.side := by
    nlinarith only [hQ.2.2.2, hc, hs]
  have dmodes : q.loU+q.side ≤ q.c*(87/50)+q.s*2 ∨
      -q.s*(87/50)+q.c*2 ≤ q.loV := by
    by_cases hu : q.loU+q.side ≤ q.c*(87/50)+q.s*2
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv =>
        hD ⟨dUlo, lt_of_not_ge hu, hv, dVhi⟩))
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
  rcases wmodes with wu | wv
  · have gap := (short_projections q (37/50) (13/50) (by norm_num)).2.1
    have dv : -q.s*(87/50)+q.c*2 ≤ q.loV := by
      rcases dmodes with du | dv
      · exfalso
        linarith only [wu, du, gap, ha]
      · exact dv
    have targetD := (short_projections q (-37/50) (14/25) (by norm_num)).2.2.2
    exact ⟨by simpa only [mul_one] using targetUlo,
      by simpa only [mul_one] using
        (show q.c+q.s*(64/25) < q.loU+q.side by
          linarith only [wu, targetW.2.1, ha]),
      by simpa only [mul_one] using targetVlo,
      by simpa only [mul_one] using
        (show -q.s+q.c*(64/25) < q.loV+q.side by
          linarith only [dv, targetD, ha])⟩
  · have vwall := mul_nonneg hs (sub_nonneg.mpr wv)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < q.c+q.s by linarith only [hsum])
    have targetUhi : q.c+q.s*(64/25) < q.loU+q.side := by
      apply lt_of_not_ge
      intro above
      have product := mul_nonneg hc (sub_nonneg.mpr above)
      nlinarith only [wall, vwall, strict, product, hsumstrong, q.unit_normal]
    exact ⟨by simpa only [mul_one] using targetUlo,
      by simpa only [mul_one] using targetUhi,
      by simpa only [mul_one] using targetVlo,
      by simpa only [mul_one] using
        (show -q.s+q.c*(64/25) < q.loV+q.side by
          linarith only [wv, targetW.2.2.2, ha])⟩

/-- No orientation restriction: reindex the four faces of the same square,
so both missing-point facts and strict ownership are preserved. -/
theorem point (q : OpenSquare) (ha : 1 < q.side) (box : InsideContainer q)
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside 1 (87/50))
    (hD : ¬ q.Inside (87/50) 2) : q.Inside 1 (64/25) := by
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
    (fun hp => hW ((hi _ _).mp hp)) (fun hp => hD ((hi _ _).mp hp)))

#print axioms point
end N12Compact.WallLowerReach

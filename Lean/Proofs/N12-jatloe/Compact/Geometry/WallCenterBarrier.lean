import Compact.Geometry.WallForcedPoint
import S12.Container

/-! Two actual missing points force a wall owner's center above the midpoint.
The proof covers the whole orientation circle by face reindexing. It needs no
angle bins, pose enclosures, upper side bound, or separating-axis premise. -/
namespace N12Compact.WallCenterBarrier
open S12 S12Pilot
set_option Elab.async false

private theorem positive_center (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side))
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside (19/25) (187/100))
    (hD : ¬ q.Inside (87/50) 2) : 2 < centerY q := by
  have hs1 : q.s ≤ 1 := by nlinarith only [q.unit_normal, sq_nonneg q.c, sq_nonneg (q.s-1)]
  have hc1 : q.c ≤ 1 := by nlinarith only [q.unit_normal, sq_nonneg q.s, sq_nonneg (q.c-1)]
  have hcs : 0 ≤ q.c*q.s := mul_nonneg hc hs
  have hsum : 1 ≤ q.c+q.s := by nlinarith only [q.unit_normal, hcs, hc, hs]
  have hsumhi : q.c+q.s ≤ 3/2 := by
    nlinarith only [q.unit_normal, sq_nonneg (q.c-q.s), hc, hs]
  have hsumstrong : 1+(4/5)*q.c*q.s ≤ q.c+q.s := by
    nlinarith only [q.unit_normal,
      mul_nonneg (sub_nonneg.mpr hsumhi) (sub_nonneg.mpr hsum)]
  have dUlo : q.loU < q.c*(87/50)+q.s*2 := by nlinarith only [hP.1, hc]
  have dVhi : -q.s*(87/50)+q.c*2 < q.loV+q.side := by
    nlinarith only [hQ.2.2.2, hc, hs]
  have dmodes : q.loU+q.side ≤ q.c*(87/50)+q.s*2 ∨
      -q.s*(87/50)+q.c*2 ≤ q.loV := by
    by_cases hu : q.loU+q.side ≤ q.c*(87/50)+q.s*2
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => hD ⟨dUlo,lt_of_not_ge hu,hv,dVhi⟩))
  have wUhi : q.c*(19/25)+q.s*(187/100) < q.loU+q.side := by
    nlinarith only [hP.2.1, hc, hs]
  have wVhi : -q.s*(19/25)+q.c*(187/100) < q.loV+q.side := by
    apply lt_of_not_ge
    intro upper
    rcases dmodes with du | dv
    · linarith only [hQ.2.1, hQ.2.2.2, du, upper, hc]
    · linarith only [upper, dv, ha, hs1, hc]
  have wmodes : q.c*(19/25)+q.s*(187/100) ≤ q.loU ∨
      -q.s*(19/25)+q.c*(187/100) ≤ q.loV := by
    by_cases hu : q.c*(19/25)+q.s*(187/100) ≤ q.loU
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => hW ⟨lt_of_not_ge hu,wUhi,hv,wVhi⟩))
  rcases wmodes with wu | wv
  · have gap := (short_projections q (49/50) (13/100) (by norm_num)).2.1
    have dv : -q.s*(87/50)+q.c*2 ≤ q.loV := by
      rcases dmodes with du | dv
      · exfalso
        linarith only [wu, du, gap, ha]
      · exact dv
    have uweight := mul_nonneg hs (sub_nonneg.mpr wu)
    have vweight := mul_nonneg hc (sub_nonneg.mpr dv)
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < q.c+q.s by linarith only [hsum])
    have ss : q.s^2 ≤ 1 := by nlinarith only [q.unit_normal, sq_nonneg q.c]
    have cs : q.c*q.s ≤ 1/2 := by nlinarith only [q.unit_normal, sq_nonneg (q.c-q.s)]
    dsimp [centerY]
    nlinarith only [uweight, vweight, strict, q.unit_normal, hsumstrong, ss, cs]
  · have wweight := mul_nonneg hs wall
    have strict := mul_pos (sub_pos.mpr ha)
      (show 0 < 1+q.s^2+q.c*q.s by nlinarith only [sq_nonneg q.s, hcs])
    have identity : q.c*centerY q =
        q.s*(q.c*q.loU-q.s*(q.loV+q.side)) + q.loV +
          q.side/2*(1+q.s^2+q.c*q.s) := by
      dsimp [centerY]
      calc
        _ = q.s*(q.c*q.loU-q.s*(q.loV+q.side)) +
            (q.c^2+q.s^2)*q.loV +
            q.side/2*((q.c^2+q.s^2)+q.s^2+q.c*q.s) := by ring
        _ = _ := by rw [q.unit_normal]; ring
    have high : 0 < q.c*(centerY q-2) := by
      nlinarith only [identity, wweight, wv, strict, sq_nonneg (q.s-19/25), hc1, hcs]
    apply lt_of_not_ge
    intro low
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr low))) high

/-- Uniform strict midpoint cut for the original square and original points. -/
theorem center_above (q : OpenSquare) (ha : 1 < q.side) (box : InsideContainer q)
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬ q.Inside (19/25) (187/100))
    (hD : ¬ q.Inside (87/50) 2) : 2 < centerY q := by
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
    (fun hp => hW ((hi _ _).mp hp)) (fun hp => hD ((hi _ _).mp hp))
  simpa only [hcy] using high

#print axioms center_above
end N12Compact.WallCenterBarrier

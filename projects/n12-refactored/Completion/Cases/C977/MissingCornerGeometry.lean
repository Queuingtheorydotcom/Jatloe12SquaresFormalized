import S12.SingletonForcing

namespace S12Completion.C977
open S12 S12Pilot
set_option maxHeartbeats 200000

/-- The three unconditional strict points already proved for a corner
    singleton in Jatloe's original model. These are distinct from the two
    stronger points derived by the separate missing-corner strengthening. -/
structure SingletonAnchors (q : S12Pilot.OpenSquare) : Prop where
  near_point : q.Inside (28 / 25) 1
  horizontal_point : q.Inside (87 / 50) 1
  lower_point : q.Inside (187 / 100) (19 / 25)

/-- The additional wall bound needed for the extended lower anchor.
    Three elementary quadratic estimates prove the cubic on the whole
    closed parameter interval; there is no sampled orientation premise. -/
theorem wall096_nonnegative (t : ℝ) (_h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ S12.wallCubic (24 / 25) (6 / 25) t := by
  dsimp [S12.wallCubic]
  by_cases hq : t ≤ 1 / 4
  · have hmul := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 / 4 - t by linarith)
    nlinarith [sq_nonneg (171 * t - 26)]
  by_cases hh : t ≤ 1 / 2
  · have hmul := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 / 2 - t by linarith)
    nlinarith [sq_nonneg (t - 1 / 4)]
  · have hmul := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - t by linarith)
    nlinarith [sq_nonneg (t - 1 / 2)]

/-- The wall estimate covers every first-quadrant unit normal, including
    both axis directions, by the original rational parametrization. -/
theorem normal_bound_096 (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hn : c ^ 2 + s ^ 2 = 1) :
    c ^ 2 + (19 / 25) * s ^ 2 + (24 / 25) * c * s ≤ c + s := by
  have h := S12.normal_bound_from_cubic (24 / 25) (6 / 25)
    wall096_nonnegative s c hs hc (by nlinarith only [hn])
  nlinarith only [h]

/-- The two extended points are strict interior points of the canonical
    missing-corner singleton. -/
structure MissingCornerPoints (q : S12Pilot.OpenSquare) : Prop where
  horizontal_point : q.Inside (91 / 50) 1
  lower_point : q.Inside (49 / 25) (19 / 25)

/-- Strict singleton anchors and a missing corner force the two extended
    points. The square is re-indexed into a positive normal frame; its
    location and geometric interior are preserved. -/
theorem missing_corner_points_of_anchors (q : OpenSquare) (ha : 1 < q.side)
    (hbox : S12.InsideContainer q)
    (hA : q.Inside 1 (457 / 500)) (hanchors : SingletonAnchors q)
    (hz : ¬q.Inside 1 1) : MissingCornerPoints q := by
  obtain ⟨r, hc, hs, hside, _, _, hinside⟩ := S12.exists_positive_frame q
  have hrA := (hinside 1 (457 / 500)).mpr hA
  have hrnear := (hinside (28 / 25) 1).mpr hanchors.near_point
  have hrhorizontal := (hinside (87 / 50) 1).mpr hanchors.horizontal_point
  have hrlower := (hinside (187 / 100) (19 / 25)).mpr hanchors.lower_point
  have hrz : ¬r.Inside 1 1 := fun hi => hz ((hinside 1 1).mp hi)
  have hra : 1 < r.side := by simpa only [hside] using ha
  have hrbox : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hi
    have hw := hbox x y ((hinside x y).mp hi)
    exact ⟨hw.1, hw.2.2.1⟩
  have hwallY := (S12.positive_frame_wall_bounds r hc hs hrbox).2
  have hywall : 0 ≤ r.s * r.loU + r.c * r.loV := by
    dsimp [S12.centerY] at hwallY
    nlinarith only [hwallY]
  rcases hrA with ⟨hA0, hA1, hA2, hA3⟩
  rcases hrnear with ⟨hN0, hN1, hN2, hN3⟩
  rcases hrhorizontal with ⟨hH0, hH1, hH2, hH3⟩
  rcases hrlower with ⟨hL0, hL1, hL2, hL3⟩
  -- Three of the corner's four bands follow from the strict anchors.
  have hz0 : r.loU < r.c + r.s := by nlinarith only [hA0, hs]
  have hz1 : r.c + r.s < r.loU + r.side := by nlinarith only [hN1, hc]
  have hz2 : r.loV < -r.s + r.c := by nlinarith only [hA2, hc]
  have hz3 : r.loV + r.side ≤ -r.s + r.c := by
    by_contra hh
    apply hrz
    change InBands r.loU r.loV r.side (r.c * 1 + r.s * 1) (-r.s * 1 + r.c * 1)
    dsimp [InBands]
    exact ⟨by simpa using hz0, by simpa using hz1,
      by simpa using hz2, by simpa using lt_of_not_ge hh⟩
  have hspos : 0 < r.s := by nlinarith only [hN3, hz3]
  have hsum : 0 < r.c + r.s := by linarith only [hc, hspos]
  have hstrict := mul_pos (show 0 < r.side - 1 by linarith only [hra]) hsum
  have hcorner := mul_nonneg hc (sub_nonneg.mpr hz3)
  have hnorm0 := S12.normal_bound_small (41 / 50) 1 1 r.c r.s
    (by norm_num) (by norm_num) (by norm_num) hc hs r.unit_normal
  have hnorm1 := normal_bound_096 r.c r.s hc hs r.unit_normal
  -- The wall estimate is strict because the side is greater than one.
  have hu0 : r.c * (91 / 50) + r.s * 1 < r.loU + r.side := by
    have hprod : 0 < r.s * (r.loU + r.side - (r.c * (91 / 50) + r.s)) := by
      nlinarith only [hcorner, hywall, hnorm0, hstrict]
    by_contra hh
    have hgap : r.loU + r.side - (r.c * (91 / 50) + r.s) ≤ 0 := by
      have hle := le_of_not_gt hh
      linarith only [hle]
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hspos.le hgap)) hprod
  have hu1 : r.c * (49 / 25) + r.s * (19 / 25) < r.loU + r.side := by
    have hprod : 0 < r.s * (r.loU + r.side -
        (r.c * (49 / 25) + r.s * (19 / 25))) := by
      nlinarith only [hcorner, hywall, hnorm1, hstrict]
    by_contra hh
    have hgap : r.loU + r.side -
        (r.c * (49 / 25) + r.s * (19 / 25)) ≤ 0 := by
      exact sub_nonpos.mpr (le_of_not_gt hh)
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hspos.le hgap)) hprod
  have hlength : (24 / 25) * r.s + (6 / 25) * r.c < 1 := by
    nlinarith only [r.unit_normal,
      sq_nonneg ((6 / 25) * r.s - (24 / 25) * r.c)]
  constructor
  · apply (hinside (91 / 50) 1).mp
    change InBands r.loU r.loV r.side _ _
    dsimp [InBands]
    exact ⟨by nlinarith only [hA0, hc, hs], hu0,
      by nlinarith only [hL2, hc, hs], by nlinarith only [hH3, hs]⟩
  · apply (hinside (49 / 25) (19 / 25)).mp
    change InBands r.loU r.loV r.side _ _
    dsimp [InBands]
    exact ⟨by nlinarith only [hL0, hc], hu1,
      by nlinarith only [hz3, hra, hlength], by nlinarith only [hL3, hs]⟩

end S12Completion.C977

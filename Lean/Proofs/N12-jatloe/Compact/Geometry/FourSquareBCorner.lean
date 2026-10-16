import Compact.Geometry.FourSquareAForced
import Compact.Geometry.LongSection
import Compact.Geometry.ThreeSquareSupport

/-! The failed horizontal section of B forces its two upper faces into one
corner and then forces a large positive angle. All premises are actual point
membership, missing points, the original side cap, and occupied cut slots. -/

namespace N12Compact.FourSquareBCorner

open S12 S12Pilot FourSquareAnchors ThreeSquare SectionCapacity LongSectionGeometry

theorem canonical_bounds (q : OpenSquare) (hc : 0 ≤ q.c)
    (hs : 0 ≤ q.s) (hsc : q.s ≤ q.c) :
    7 / 10 ≤ q.c ∧ q.c ≤ 1 ∧ q.s ≤ 1 ∧
    q.c + q.s ≤ 10 / 7 ∧ q.c * q.s ≤ 1 / 2 := by
  have h := q.unit_normal
  have hc1 : q.c ≤ 1 := by nlinarith only [h, sq_nonneg q.s]
  have hs1 : q.s ≤ 1 := by nlinarith only [h, sq_nonneg q.c]
  have cs := mul_nonneg (sub_nonneg.mpr hsc) (add_nonneg hc hs)
  exact ⟨by nlinarith only [h, cs, hc], hc1, hs1,
    by nlinarith only [h, sq_nonneg (q.c - q.s), hc, hs],
    by nlinarith only [h, sq_nonneg (q.c - q.s)]⟩

theorem no_long_section (A B L R : OpenSquare)
    (box : InsideContainer B)
    (left : ClosedInside L 1 (12 / 5))
    (middle : A.Inside 2 (12 / 5))
    (right : ClosedInside R 3 (12 / 5))
    (bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y))
    (ba : ∀ x y, ¬ (B.Inside x y ∧ A.Inside x y))
    (br : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)) :
    ¬ LongSection B (12 / 5) := by
  intro hsection
  obtain ⟨j, hj⟩ := section_hits B (12 / 5) box hsection
  have hleft := ClosedPointExclusion.outside_of_closed B L _ _ bl left
  have hright := ClosedPointExclusion.outside_of_closed B R _ _ br right
  fin_cases j
  · exact hleft (by norm_num at hj ⊢; exact hj)
  · exact ba _ _ ⟨by norm_num at hj ⊢; exact hj, middle⟩
  · exact hright (by norm_num at hj ⊢; exact hj)

theorem center_above_radius (B : OpenSquare)
    (hc : 0 ≤ B.c) (hs : 0 ≤ B.s) (hsc : B.s ≤ B.c)
    (ha : 1 < B.side) (cap : B.side ≤ 1001 / 1000)
    (top : ClosedInside B (8 / 5) 3)
    (short : ¬ LongSection B (12 / 5)) :
    12 / 5 + (B.c + B.s - 2 * B.c * B.s) / 2 < centerY B := by
  obtain ⟨hc7, hc1, hs1, hsum, hprod⟩ := canonical_bounds B hc hs hsc
  have htop := (abs_le.mp (closed_support B (8 / 5) 3 0 1 top)).2
  simp only [supportRadius, zero_mul, one_mul, zero_add, neg_zero,
    abs_of_nonneg hs, abs_of_nonneg hc] at htop
  have hmul := mul_le_mul_of_nonneg_left cap (add_nonneg hc hs)
  have low : 12 / 5 - (B.c + B.s - 2 * B.c * B.s) / 2 ≤ centerY B := by
    nlinarith only [htop, hmul, hsum, hprod]
  by_contra high
  apply short
  apply horizontal_long_section B _ ha
  simp only [sectionRadius, abs_of_nonneg hc, abs_of_nonneg hs,
    abs_of_nonneg (mul_nonneg hc hs)]
  apply abs_le.mpr
  constructor <;> linarith only [low, le_of_not_gt high]

/-- Only the two upper corner faces survive; the alternative top V face
would already give a long section. -/
theorem upper_corner (B : OpenSquare)
    (hc : 0 < B.c) (hs : 0 ≤ B.s) (hsc : B.s ≤ B.c)
    (ha : 1 < B.side) (cap : B.side ≤ 1001 / 1000)
    (bottom : ClosedInside B (33 / 20) (47 / 20))
    (top : ClosedInside B (8 / 5) 3)
    (topRight : ClosedInside B (87 / 50) 3)
    (missingLeft : ¬ B.Inside 1 (1543 / 500))
    (missingRight : ¬ B.Inside 2 (1543 / 500))
    (short : ¬ LongSection B (12 / 5)) :
    B.loU + B.side ≤ 2 * B.c + (1543 / 500) * B.s ∧
    B.loV + B.side ≤ -B.s + (1543 / 500) * B.c := by
  obtain ⟨hc7, hc1, hs1, hsum, hprod⟩ := canonical_bounds B hc.le hs hsc
  have high := center_above_radius B hc.le hs hsc ha cap top short
  have pUhi : B.c + B.s * (1543 / 500) < B.loU + B.side := by
    nlinarith only [top.2.1, hsc, hc]
  have pVlo : B.loV < -B.s + B.c * (1543 / 500) := by
    nlinarith only [top.2.2.1, hs, hc]
  have pMode : B.c + B.s * (1543 / 500) ≤ B.loU ∨
      B.loV + B.side ≤ -B.s + B.c * (1543 / 500) := by
    by_cases h : B.c + B.s * (1543 / 500) ≤ B.loU
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt (fun hv => missingLeft
        ⟨by linarith only [lt_of_not_ge h], by linarith only [pUhi],
          by linarith only [pVlo], by linarith only [hv]⟩))
  have qUlo : B.loU < 2 * B.c + B.s * (1543 / 500) := by
    nlinarith only [bottom.1, hc, hs]
  have qVlo : B.loV < -2 * B.s + B.c * (1543 / 500) := by
    nlinarith only [bottom.2.2.1, hsc, hc]
  have qMode : B.loU + B.side ≤ 2 * B.c + B.s * (1543 / 500) ∨
      B.loV + B.side ≤ -2 * B.s + B.c * (1543 / 500) := by
    by_cases h : B.loU + B.side ≤ 2 * B.c + B.s * (1543 / 500)
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt (fun hv => missingRight
        ⟨by linarith only [qUlo], by linarith only [lt_of_not_ge h],
          by linarith only [qVlo], by linarith only [hv]⟩))
  have notV : ¬ B.loV + B.side ≤ -2 * B.s + B.c * (1543 / 500) := by
    intro hv
    have ratio : 130 * B.s ≤ 43 * B.c := by
      linarith only [hv, topRight.2.2.2]
    have squareRatio := mul_nonneg (sub_nonneg.mpr ratio)
      (by positivity : 0 ≤ 43 * B.c + 130 * B.s)
    have c94 : 47 / 50 ≤ B.c := by
      nlinarith only [B.unit_normal, squareRatio, hc]
    have prodBound : B.c * B.s ≤ 43 / 130 := by
      have hm := mul_le_mul_of_nonneg_left ratio hc.le
      nlinarith only [hm, B.unit_normal, sq_nonneg B.s]
    have u := mul_le_mul_of_nonneg_left topRight.1 hs
    have v := mul_le_mul_of_nonneg_left hv hc.le
    have a := mul_nonneg (by linarith only [ha] : 0 ≤ B.side - 1)
      (sub_nonneg.mpr hsc)
    have center : centerY B = B.s * (B.loU + B.side / 2) +
        B.c * (B.loV + B.side / 2) := rfl
    nlinarith only [u, v, center, B.unit_normal, a, high, c94, prodBound,
      sq_nonneg B.s]
  have hu := qMode.resolve_right notV
  refine ⟨by linarith only [hu], ?_⟩
  rcases pMode with hp | hp
  · nlinarith only [hp, hu, ha, hc1]
  · linarith only [hp]

theorem corner_steep (B : OpenSquare)
    (hc : 0 ≤ B.c) (hs : 0 ≤ B.s) (hsc : B.s ≤ B.c)
    (ha : 1 < B.side)
    (high : 12 / 5 + (B.c + B.s - 2 * B.c * B.s) / 2 < centerY B)
    (upperU : B.loU + B.side ≤ 2 * B.c + (1543 / 500) * B.s)
    (upperV : B.loV + B.side ≤ -B.s + (1543 / 500) * B.c) :
    5 / 4 < B.c + B.s ∧ 9 / 32 < B.s := by
  obtain ⟨hc7, hc1, hs1, hsum, hprod⟩ := canonical_bounds B hc hs hsc
  have u := mul_le_mul_of_nonneg_left upperU hs
  have v := mul_le_mul_of_nonneg_left upperV hc
  have a := mul_nonneg (by linarith only [ha] : 0 ≤ B.side - 1)
    (add_nonneg hc hs)
  have identity : centerY B = B.s * (B.loU + B.side / 2) +
      B.c * (B.loV + B.side / 2) := rfl
  have bend : B.c + B.s - 2 * B.c * B.s < 343 / 500 := by
    nlinarith only [u, v, a, high, identity, B.unit_normal]
  have sumLow : 1 ≤ B.c + B.s := by
    nlinarith only [B.unit_normal, mul_nonneg hc hs, hc, hs]
  have steep : 5 / 4 < B.c + B.s := by
    by_contra h
    have hh := mul_nonneg (by linarith only [sumLow] : 0 ≤ B.c + B.s - 1)
      (by linarith only [h] : 0 ≤ 5 / 4 - (B.c + B.s))
    nlinarith only [hh, bend, B.unit_normal, h]
  have prod : 9 / 32 < B.c * B.s := by
    nlinarith only [steep, B.unit_normal, sq_nonneg (B.c + B.s - 5 / 4)]
  have mul := mul_le_mul_of_nonneg_right hc1 hs
  exact ⟨steep, by linarith only [prod, mul]⟩

/-- The two occupied points below B turn the steep corner into a strong
height inequality and a single coarse angle bound. -/
theorem forced_lower_V (B : OpenSquare)
    (hc : 0 < B.c) (hs : 0 ≤ B.s) (hsc : B.s ≤ B.c)
    (ha : 1 < B.side) (steep : 9 / 32 < B.s)
    (bottom : ClosedInside B (33 / 20) (47 / 20))
    (top : ClosedInside B (8 / 5) 3)
    (topRight : ClosedInside B (87 / 50) 3)
    (rowMissing : ¬ B.Inside 1 (12 / 5))
    (targetMissing : ¬ B.Inside 2 (5 / 2))
    (upperV : B.loV + B.side ≤ -B.s + (1543 / 500) * B.c) :
    -2 * B.s + (5 / 2) * B.c ≤ B.loV ∧
    B.side ≤ B.s + (293 / 500) * B.c ∧ 34 / 25 < B.c + B.s := by
  obtain ⟨hc7, hc1, hs1, hsum, hprod⟩ := canonical_bounds B hc.le hs hsc
  have rowUhi : B.c + B.s * (12 / 5) < B.loU + B.side := by
    nlinarith only [top.2.1, hc, hs]
  have rowVlo : B.loV < -B.s + B.c * (12 / 5) := by
    nlinarith only [bottom.2.2.1, hc, hs]
  have targetUlo : B.loU < 2 * B.c + B.s * (5 / 2) := by
    nlinarith only [bottom.1, hc, hs]
  have targetVhi : -2 * B.s + B.c * (5 / 2) < B.loV + B.side := by
    nlinarith only [top.2.2.2, hc, hs]
  have rowLow : B.c + B.s * (12 / 5) ≤ B.loU := by
    by_contra h
    have rowHigh : B.loV + B.side ≤ -B.s + B.c * (12 / 5) :=
      le_of_not_gt (fun hv => rowMissing
        ⟨by linarith only [lt_of_not_ge h], by linarith only [rowUhi],
          by linarith only [rowVlo], by linarith only [hv]⟩)
    have diagonal : B.c = B.s := by
      nlinarith only [rowHigh, top.2.2.2, hsc]
    apply targetMissing
    refine ⟨by linarith only [targetUlo], ?_, ?_, by linarith only [targetVhi]⟩
    · nlinarith only [topRight.2.1, diagonal, hc]
    · nlinarith only [rowHigh, ha, hc1, diagonal]
  have narrow : B.c + B.s / 10 < 1 := by
    apply lt_of_not_ge
    intro h
    have bound : 1 - B.s / 10 ≤ B.c := by linarith only [h]
    have square := mul_nonneg (sub_nonneg.mpr bound)
      (by nlinarith only [hc, hs1] : 0 ≤ B.c + (1 - B.s / 10))
    have positive : 0 < B.s * ((101 / 100) * B.s - 1 / 5) :=
      mul_pos (by linarith only [steep]) (by linarith only [steep])
    nlinarith only [square, B.unit_normal, positive]
  have targetUhi : 2 * B.c + B.s * (5 / 2) < B.loU + B.side := by
    nlinarith only [rowLow, narrow, ha]
  have low : -2 * B.s + B.c * (5 / 2) ≤ B.loV :=
    le_of_not_gt (fun hv => targetMissing
      ⟨by linarith only [targetUlo], by linarith only [targetUhi],
        by linarith only [hv], by linarith only [targetVhi]⟩)
  have height : B.side ≤ B.s + (293 / 500) * B.c := by
    linarith only [low, upperV]
  refine ⟨by linarith only [low], height, ?_⟩
  apply lt_of_not_ge
  intro h
  have sumSquare := mul_nonneg
    (by linarith only [h] : 0 ≤ 34 / 25 - (B.c + B.s))
    (by linarith only [hc, hs] : 0 ≤ 34 / 25 + (B.c + B.s))
  have diff : 19 / 50 < B.c - B.s := by
    apply lt_of_not_ge
    intro hd
    have diffSquare := mul_nonneg
      (by linarith only [hd] : 0 ≤ 19 / 50 - (B.c - B.s))
      (by linarith only [hsc] : 0 ≤ 19 / 50 + (B.c - B.s))
    nlinarith only [B.unit_normal, sumSquare, diffSquare]
  nlinarith only [height, ha, diff, h]

end N12Compact.FourSquareBCorner

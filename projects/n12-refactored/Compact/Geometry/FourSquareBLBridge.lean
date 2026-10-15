import Compact.Geometry.FourSquareBCorner
import Compact.Geometry.BLLongitudinal

/-! Geometric elimination of the wrong lower face of L, and exact support
bounds connecting the original B/L squares to the small scalar contradiction.
No interval table or angle enumeration appears in this bridge. -/

namespace N12Compact.FourSquareBLBridge

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare C977ChainBridge

theorem left_wall (q : OpenSquare) (hc : 0 ≤ q.c) (box : InsideContainer q) :
    q.side * (q.c + |q.s|) / 2 ≤ centerX q := by
  have hw : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y :=
    fun x y hp => ⟨(box x y hp).1, (box x y hp).2.2.1⟩
  by_cases hs : 0 ≤ q.s
  · simpa only [abs_of_nonneg hs] using (positive_frame_wall_bounds q hc hs hw).1
  · have ht : ∀ x y, (turnFrame q).Inside x y → 0 ≤ x ∧ 0 ≤ y := by
      intro x y hp
      exact hw x y ((turnFrame_inside q x y).mp hp)
    have bound := (positive_frame_wall_bounds (turnFrame q)
      (by dsimp [turnFrame]; linarith) hc ht).1
    rw [turnFrame_centerX] at bound
    simp only [turnFrame, abs_of_nonpos (le_of_not_ge hs)]
    dsimp [turnFrame] at bound
    linarith

private theorem radius (q r : OpenSquare) :
    pairRadius q r = q.side / 2 + supportRadius r q.c q.s := by
  have he : -q.c * r.s + q.s * r.c = -normalCross q r := by
    unfold normalCross
    ring
  simp only [pairRadius, supportRadius, normalDot, he, abs_neg]

theorem right_axis_cap (q r : OpenSquare)
    (sep : pairRadius q r ≤
      q.c * (centerX q - centerX r) + q.s * (centerY q - centerY r)) :
    q.c * centerX r + q.s * centerY r + supportRadius r q.c q.s ≤ q.loU := by
  have he := (center_coordinates q).1
  rw [radius] at sep
  linarith only [he, sep]

theorem left_axis_cap (q r : OpenSquare)
    (sep : pairRadius q r ≤
      q.c * (centerX r - centerX q) + q.s * (centerY r - centerY q)) :
    q.loU + q.side ≤ q.c * centerX r + q.s * centerY r -
      supportRadius r q.c q.s := by
  have he := (center_coordinates q).1
  rw [radius] at sep
  linarith only [he, sep]

theorem dot_nonneg (B L : OpenSquare)
    (bc : 0 ≤ B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 ≤ L.c) (lsc : |L.s| ≤ L.c) :
    0 ≤ B.c * L.c + B.s * L.s := by
  have h1 := mul_nonneg (sub_nonneg.mpr bsc) lc
  have h2 := mul_nonneg bs (by linarith only [(abs_le.mp lsc).1] : 0 ≤ L.c + L.s)
  nlinarith only [h1, h2]

/-- If W uses the lower U face of a left square, the other original
missing point forces the lower V face, and hence a fixed interior point.
This lemma retains both signs of the canonical L frame. -/
theorem left_point_of_lower_U (L : OpenSquare)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c) (ha : 1 < L.side)
    (ll : ClosedInside L (457 / 500) 2)
    (lt : ClosedInside L 1 (12 / 5))
    (missingRight : ¬ L.Inside (33 / 20) (33 / 20))
    (wrong : L.c * (19 / 25) + L.s * (187 / 100) ≤ L.loU) :
    L.Inside (13 / 10) (12 / 5) := by
  have labs := abs_le.mp lsc
  have pUlo : L.loU < L.c * (33 / 20) + L.s * (33 / 20) := by
    nlinarith only [ll.1, labs.2, lc]
  have pVhi : -L.s * (33 / 20) + L.c * (33 / 20) < L.loV + L.side := by
    nlinarith only [lt.2.2.2, labs.1, lc]
  have span := (short_projections L (89 / 100) (-(11 / 50)) (by norm_num)).2.1
  have pUhi : L.c * (33 / 20) + L.s * (33 / 20) < L.loU + L.side := by
    linarith only [span, wrong, ha]
  have pVlo : -L.s * (33 / 20) + L.c * (33 / 20) ≤ L.loV :=
    le_of_not_gt (fun hv => missingRight ⟨pUlo, pUhi, hv, pVhi⟩)
  have uSpan := (short_projections L (27 / 50) (53 / 100) (by norm_num)).2.1
  have vSpan := (short_projections L (-(7 / 20)) (3 / 4) (by norm_num)).2.2.2
  exact ⟨by nlinarith only [lt.1, lc], by linarith only [wrong, uSpan, ha],
    by nlinarith only [ll.2.2.1, labs.2, lc],
    by linarith only [pVlo, vSpan, ha]⟩

/-- B's two upper corner faces force the same point, with uniform strict
room independent of its angle. -/
theorem right_point_of_upper_corner (B : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (ha : 1 < B.side)
    (bottom : ClosedInside B (33 / 20) (47 / 20))
    (top : ClosedInside B (8 / 5) 3)
    (upperU : B.loU + B.side ≤ 2 * B.c + (1543 / 500) * B.s)
    (upperV : B.loV + B.side ≤ -B.s + (1543 / 500) * B.c) :
    B.Inside (13 / 10) (12 / 5) := by
  have uSpan := (short_projections B (7 / 10) (343 / 500) (by norm_num)).2.1
  have vSpan := (short_projections B (-(3 / 10)) (343 / 500) (by norm_num)).2.2.2
  exact ⟨by linarith only [upperU, uSpan, ha],
    by nlinarith only [bottom.2.1, bc, bsc],
    by linarith only [upperV, vSpan, ha],
    by nlinarith only [top.2.2.2, bc, bsc]⟩

/-- W must lie below L's lower V face: its other possible face would put
(1.3,2.4) strictly inside both actual squares. No separating-axis branch is
needed for this reduction. -/
theorem missing_below_V (B L : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (haB : 1 < B.side) (haL : 1 < L.side)
    (bottom : ClosedInside B (33 / 20) (47 / 20))
    (top : ClosedInside B (8 / 5) 3)
    (ll : ClosedInside L (457 / 500) 2)
    (lt : ClosedInside L 1 (12 / 5))
    (missing : ¬ L.Inside (19 / 25) (187 / 100))
    (missingRight : ¬ L.Inside (33 / 20) (33 / 20))
    (upperU : B.loU + B.side ≤ 2 * B.c + (1543 / 500) * B.s)
    (upperV : B.loV + B.side ≤ -B.s + (1543 / 500) * B.c)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)) :
    -L.s * (19 / 25) + L.c * (187 / 100) ≤ L.loV := by
  have labs := abs_le.mp lsc
  have wu : L.c * (19 / 25) + L.s * (187 / 100) < L.loU + L.side := by
    nlinarith only [ll.2.1, labs.1, lc]
  have wv : -L.s * (19 / 25) + L.c * (187 / 100) < L.loV + L.side := by
    nlinarith only [lt.2.2.2, labs.2, lc]
  by_contra hn
  have wrong : L.c * (19 / 25) + L.s * (187 / 100) ≤ L.loU :=
    le_of_not_gt (fun hu => missing ⟨hu, wu, lt_of_not_ge hn, wv⟩)
  exact apart _ _ ⟨right_point_of_upper_corner B bc bs bsc haB bottom top upperU upperV,
    left_point_of_lower_U L lc lsc haL ll lt missingRight wrong⟩

theorem left_upper_bounds (L : OpenSquare) (lc : 0 < L.c)
    (box : InsideContainer L)
    (ll : ClosedInside L (457 / 500) 2)
    (lowV : -L.s * (19 / 25) + L.c * (187 / 100) ≤ L.loV) :
    (0 ≤ L.s → L.side * (1 + L.s / L.c) + (187 / 100) * L.s -
      (19 / 25) * L.s ^ 2 / L.c ≤ L.loU + L.side) ∧
    (L.s ≤ 0 → L.side - (457 / 500) * L.s ^ 2 / L.c + 2 * L.s ≤
      L.loU + L.side) := by
  have wall := left_wall L lc.le box
  have identity : L.c * (L.loU + L.side) =
      centerX L + L.s * (L.loV + L.side / 2) + L.side * L.c / 2 := by
    dsimp [centerX]
    ring
  constructor
  · intro ls
    rw [abs_of_nonneg ls] at wall
    have scaled := mul_le_mul_of_nonneg_left lowV ls
    have clear : (L.side * (1 + L.s / L.c) + (187 / 100) * L.s -
        (19 / 25) * L.s ^ 2 / L.c) * L.c =
        L.side * (L.c + L.s) + (187 / 100) * L.s * L.c -
          (19 / 25) * L.s ^ 2 := by
      field_simp [ne_of_gt lc]
      <;> ring
    apply (mul_le_mul_right lc).mp
    rw [clear]
    nlinarith only [wall, identity, scaled]
  · intro ls
    rw [abs_of_nonpos ls] at wall
    have scaled := mul_le_mul_of_nonpos_left ll.2.2.1 ls
    have clear : (L.side - (457 / 500) * L.s ^ 2 / L.c + 2 * L.s) * L.c =
        L.side * L.c - (457 / 500) * L.s ^ 2 + 2 * L.s * L.c := by
      field_simp [ne_of_gt lc]
      <;> ring
    apply (mul_le_mul_right lc).mp
    rw [clear]
    nlinarith only [wall, identity, scaled]

theorem minimum_projection (B L : OpenSquare)
    (hd : 0 ≤ B.c * L.c + B.s * L.s) :
    L.c * centerX B + L.s * centerY B - supportRadius B L.c L.s =
      (B.c * L.c + B.s * L.s) * B.loU +
      (B.c * L.s - B.s * L.c) * (B.loV + B.side / 2) -
      B.side / 2 * |B.c * L.s - B.s * L.c| := by
  have he : L.c * B.c + L.s * B.s = B.c * L.c + B.s * L.s := by ring
  have ht : -L.c * B.s + L.s * B.c = B.c * L.s - B.s * L.c := by ring
  simp only [supportRadius, he, ht, abs_of_nonneg hd]
  dsimp [centerX, centerY]
  ring

theorem right_minimum_bounds (B L : OpenSquare)
    (hd : 0 ≤ B.c * L.c + B.s * L.s)
    (upperU : B.loU + B.side ≤ 2 * B.c + (1543 / 500) * B.s)
    (upperV : B.loV + B.side ≤ -B.s + (1543 / 500) * B.c)
    (lowerV : -2 * B.s + (5 / 2) * B.c ≤ B.loV)
    (axis : pairRadius L B ≤
      L.c * (centerX B - centerX L) + L.s * (centerY B - centerY L)) :
    (0 ≤ B.c * L.s - B.s * L.c → L.loU + L.side ≤
      L.c * (1 + B.c ^ 2) + L.s * (1543 / 500 + B.c * B.s) -
      B.side * ((B.c * L.c + B.s * L.s) + (B.c * L.s - B.s * L.c))) ∧
    (B.c * L.s - B.s * L.c ≤ 0 → L.loU + L.side ≤
      L.c * (2 + (293 / 500) * B.c * B.s) +
      L.s * (5 / 2 + (293 / 500) * B.s ^ 2) -
      B.side * ((B.c * L.c + B.s * L.s) - (B.c * L.s - B.s * L.c))) := by
  have cap := left_axis_cap L B axis
  rw [minimum_projection B L hd] at cap
  have u := mul_le_mul_of_nonneg_left upperU hd
  have unC := congrArg (fun x : ℝ => L.c * x) B.unit_normal
  have unS := congrArg (fun x : ℝ => L.s * x) B.unit_normal
  dsimp only at unC unS
  constructor
  · intro ht
    rw [abs_of_nonneg ht] at cap
    have v := mul_le_mul_of_nonneg_left upperV ht
    nlinarith only [cap, u, v, unC, unS]
  · intro ht
    rw [abs_of_nonpos ht] at cap
    have v := mul_le_mul_of_nonpos_left lowerV ht
    nlinarith only [cap, u, v, unC, unS]

end N12Compact.FourSquareBLBridge

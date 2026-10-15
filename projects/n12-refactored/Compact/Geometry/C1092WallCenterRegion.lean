import S12.CenterLocalization

/-! Source-only candidate for the geometric entrance to the complementary
`centerX ≥ 1` branch of the C1092 wall-point argument. No Lean replay yet.
Only actual marker ownership, missing markers and the original side cap
occur in the hypotheses. No saved center polygon is assumed. -/

namespace N12Compact.C1092WallCenterRegion

open S12 S12Pilot

/-- The owned wall marker is sufficiently far from the diagonal that its
owner's center is strictly above that diagonal. The same circumradius bound
places its center strictly to the left of the two nearby central markers. -/
theorem coarse_bounds (q : OpenSquare) (cap : q.side ≤ 1001/1000)
    (owned : q.Inside (457/500) 2) :
    centerX q < 33/20 ∧ centerX q < centerY q := by
  have hd := inside_center_distance q (457/500) 2 owned
  have hcap : q.side^2 ≤ (1001/1000:ℝ)^2 := by
    have hh := mul_nonneg (sub_nonneg.mpr cap)
      (show 0 ≤ (1001/1000:ℝ)+q.side by linarith [q.side_pos])
    nlinarith only [hh]
  constructor
  · by_contra hx
    have hx' : 33/20 ≤ centerX q := le_of_not_gt hx
    have hp := mul_nonneg (show 0 ≤ centerX q-33/20 by linarith)
      (show 0 ≤ centerX q-457/500+92/125 by linarith)
    nlinarith only [hd,hcap,hp,sq_nonneg (2-centerY q)]
  · by_contra hxy
    have hxy' : centerY q ≤ centerX q := le_of_not_gt hxy
    have hsum : 543/500 ≤ (centerX q-457/500)+(2-centerY q) := by linarith
    have hp := mul_nonneg (sub_nonneg.mpr hsum)
      (show 0 ≤ (centerX q-457/500)+(2-centerY q)+543/500 by linarith)
    nlinarith only [hd,hcap,hp,
      sq_nonneg ((centerX q-457/500)-(2-centerY q))]

/-- Every original wall-marker owner in the closed right branch has its
center in the exact four-sided region used by the old center-cover code.
Marker0 is needed to rule out its lower complementary triangle; marker11
will be used by the subsequent point-forcing argument. -/
theorem original_marker_entrance (q : OpenSquare) (ha : 1 < q.side)
    (cap : q.side ≤ 1001/1000) (owned : q.Inside (457/500) 2)
    (outside0 : ¬ q.Inside 1 (457/500))
    (outside1 : ¬ q.Inside (457/500) 1)
    (outside8 : ¬ q.Inside (33/20) (33/20))
    (hx : 1 ≤ centerX q) (hy : centerY q ≤ 2) :
    centerX q ≤ 33/20 ∧
      (325/368)*centerX q+1419/7360 ≤ centerY q := by
  obtain ⟨hxa,hxy⟩ := coarse_bounds q cap owned
  refine ⟨hxa.le,?_⟩
  by_contra hline
  have hline' : centerY q < (325/368)*centerX q+1419/7360 := lt_of_not_ge hline
  have h0 : 0 ≤ tri0w0 (centerX q) (centerY q) := by
    dsimp [tri0w0]; linarith
  have h1 : 0 ≤ tri0w1 (centerX q) (centerY q) := by
    dsimp [tri0w1]; linarith
  have h2 : 0 ≤ tri0w2 (centerX q) (centerY q) := by
    dsimp [tri0w2]; linarith
  rcases triangle0_hit q ha h0 h1 h2 with h | h | h
  · exact outside0 (by simpa [Owns,marker] using h)
  · exact outside1 (by simpa [Owns,marker] using h)
  · exact outside8 (by simpa [Owns,marker] using h)

#print axioms original_marker_entrance

end N12Compact.C1092WallCenterRegion

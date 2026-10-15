import Compact.Geometry.BorderEndpoint
import S12.WallGeometry
import S12.Container

/-!
Bridge to the original `S12Pilot.OpenSquare` model. The square, ownership,
containment, and centered-band equivalence come from the original proof.
No certificate, discretized pose, alternative packing model, or additional
axiom is introduced. Applications must still establish the stated angle and
center bounds from the actual case entrance. This bridge is uncompiled.
-/

namespace N12Compact.OriginalBorderEndpoint

open S12 S12Pilot

/-- The upper transverse face is the only possible missing-point face.
This short argument is the original C696 `upper_face_of_not_inside` argument,
isolated here so its unrelated separator and angle-data imports are unnecessary.
Original source blob: `65b06577ab526addf4128562dd8f43c718883683`.
-/
theorem upper_face_of_not_inside (q : OpenSquare) (t b u : ℝ)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s) (hb : b ≤ 1) (hu : t ≤ u)
    (hbelow : q.Inside t b) (hright : q.Inside u 1)
    (hnot : ¬ q.Inside t 1) :
    q.side / 2 ≤ -q.s * (t - centerX q) + q.c * (1 - centerY q) := by
  have hb' := (inside_centered_iff q t b).mp hbelow
  have hu' := (inside_centered_iff q u 1).mp hright
  have hcb := mul_nonneg hc (sub_nonneg.mpr hb)
  have hsb := mul_nonneg hs (sub_nonneg.mpr hb)
  have hcu := mul_nonneg hc (sub_nonneg.mpr hu)
  by_contra hmissing
  have hupper := lt_of_not_ge hmissing
  apply hnot
  apply (inside_centered_iff q t 1).mpr
  dsimp [InBands] at hb' hu' ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hb'.1, hsb]
  · nlinarith only [hu'.2.1, hcu]
  · nlinarith only [hb'.2.2.1, hcb]
  · linarith only [hupper]

/-- At zero canonical angle, coordinatewise rectangle membership combines
the x-coordinate of one strict point and the y-coordinate of another. This
handles the axis-aligned endpoint directly, without division by the sine. -/
theorem zero_angle_crossing_point (q : OpenSquare) (t b u : ℝ)
    (hc : q.c = 1) (hs : q.s = 0)
    (hbelow : q.Inside t b) (hright : q.Inside u 1) : q.Inside t 1 := by
  have hb := (inside_centered_iff q t b).mp hbelow
  have hr := (inside_centered_iff q u 1).mp hright
  apply (inside_centered_iff q t 1).mpr
  dsimp [InBands] at hb hr ⊢
  simp only [hc, hs, one_mul, zero_mul, zero_add, add_zero, neg_zero] at hb hr ⊢
  exact ⟨hb.1, hb.2.1, hr.2.2.1, hr.2.2.2⟩

/-- The actual target contains both its center abscissa and the point past
`t+side` on the test row. The upper-face premise is derived from strict owned
points and failure to own `(t,1)`; the bottom premise is derived from actual
container containment. The closed upper angle endpoint `z=2/7` is included.
-/
theorem positive_endpoint_points (q : OpenSquare) (t b u z : ℝ)
    (ha : 1 < q.side) (hbox : InsideContainer q)
    (hz : 0 < z) (hzmax : z ≤ 2 / 7)
    (hcos : q.c = (1 - z ^ 2) / (1 + z ^ 2))
    (hsin : q.s = 2 * z / (1 + z ^ 2))
    (hcenter : centerX q ≤ t + 1)
    (hb : b ≤ 1) (hu : t ≤ u)
    (hbelow : q.Inside t b) (hright : q.Inside u 1)
    (hmissing : ¬ q.Inside t 1) :
    q.Inside (centerX q) (45 / 98) ∧
      q.Inside (t + q.side) (45 / 98) := by
  have hangle := BorderEndpoint.half_angle_band z hz hzmax
  dsimp only at hangle
  rw [← hcos, ← hsin] at hangle
  rcases hangle with ⟨hc, hs, hsc, hunit, hlo, hhi, hhalf⟩
  have hface := upper_face_of_not_inside
    q t b u hc.le hs.le hb hu hbelow hright hmissing
  have hbottom := (positive_frame_wall_bounds q hc.le hs.le (by
    intro x y hin
    exact ⟨(hbox x y hin).1, (hbox x y hin).2.2.1⟩)).2
  have endpoints := BorderEndpoint.positive_endpoints q.side q.c q.s
    (centerX q) (centerY q) t (45 / 98) ha hc hs hsc hunit hlo hhi hhalf
    hcenter (by nlinarith only [hface]) hbottom
  dsimp only at endpoints
  rcases endpoints with ⟨hheight, _, hleft, hcenterRight, hrightU, hrightV⟩
  have inside : ∀ x : ℝ, centerX q ≤ x → x ≤ t + q.side → q.Inside x (45 / 98) := by
    intro x hxl hxr
    apply (inside_centered_iff q x (45 / 98)).mpr
    have bands := BorderEndpoint.inside_bands_of_endpoints q.side q.c q.s
      (centerX q) (centerY q) (45 / 98) x
      (by linarith only [ha]) hc hs hheight hxl
      (lt_of_lt_of_le hleft hxl) (lt_of_le_of_lt hxr hrightU)
      (lt_of_le_of_lt hxr hrightV)
    dsimp [InBands]
    exact ⟨bands.1, by linarith only [bands.2.1],
      bands.2.2.1, by linarith only [bands.2.2.2]⟩
  exact ⟨inside (centerX q) le_rfl hcenterRight.le,
    inside (t + q.side) hcenterRight.le le_rfl⟩

end N12Compact.OriginalBorderEndpoint

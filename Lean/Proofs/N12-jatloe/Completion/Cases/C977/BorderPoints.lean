import S12.TriangleCover
import S12.Packing

/-!
Sound local rules for the conditional border-point deduction. These rules
operate on the original strict square model. Enclosure bounds needed by an
application must be supplied separately; no saved numerical pose is assumed.
-/
namespace S12Completion.C977
open S12 S12Pilot

set_option maxHeartbeats 0

/-- Two compulsory points below and to the right of a border point leave
only the upper-V escape in a nonnegative signed frame. Equality of an
excluding face is retained. -/
theorem border_missing_positive_face (q : OpenSquare) (t x y : ℝ)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s) (hx : t ≤ x) (hy : y ≤ 1)
    (hbelow : q.Inside t y) (hright : q.Inside x 1)
    (hmissing : ¬q.Inside t 1) :
    q.loV + q.side ≤ -q.s*t+q.c := by
  rcases hbelow with ⟨b0,b1,b2,b3⟩
  rcases hright with ⟨r0,r1,r2,r3⟩
  have hyprod := mul_nonneg hs (sub_nonneg.mpr hy)
  have hxprod := mul_nonneg hc (sub_nonneg.mpr hx)
  have hxprod' := mul_nonneg hs (sub_nonneg.mpr hx)
  have hu0 : q.loU < q.c*t+q.s*1 := by nlinarith only [b0,hyprod]
  have hu1 : q.c*t+q.s*1 < q.loU+q.side := by nlinarith only [r1,hxprod]
  have hv0 : q.loV < -q.s*t+q.c*1 := by nlinarith only [r2,hxprod']
  by_contra hh
  have hv1 : -q.s*t+q.c*1 < q.loV+q.side := by
    have := lt_of_not_ge hh
    simpa using this
  exact hmissing ⟨hu0,hu1,hv0,hv1⟩

/-- The corresponding negative signed frame leaves only the lower-U
escape. The orientation-zero boundary is included in both statements. -/
theorem border_missing_negative_face (q : OpenSquare) (t x y : ℝ)
    (hc : 0 ≤ q.c) (hs : q.s ≤ 0) (hx : t ≤ x) (hy : y ≤ 1)
    (hbelow : q.Inside t y) (hright : q.Inside x 1)
    (hmissing : ¬q.Inside t 1) :
    q.c*t+q.s ≤ q.loU := by
  rcases hbelow with ⟨b0,b1,b2,b3⟩
  rcases hright with ⟨r0,r1,r2,r3⟩
  have hyprod := mul_nonneg (neg_nonneg.mpr hs) (sub_nonneg.mpr hy)
  have hyprod' := mul_nonneg hc (sub_nonneg.mpr hy)
  have hxprod := mul_nonneg (neg_nonneg.mpr hs) (sub_nonneg.mpr hx)
  have hu1 : q.c*t+q.s*1 < q.loU+q.side := by nlinarith only [b1,hyprod]
  have hv0 : q.loV < -q.s*t+q.c*1 := by nlinarith only [b2,hyprod']
  have hv1 : -q.s*t+q.c*1 < q.loV+q.side := by nlinarith only [r3,hxprod]
  by_contra hh
  have hu0 : q.loU < q.c*t+q.s*1 := by
    have := lt_of_not_ge hh
    simpa using this
  exact hmissing ⟨hu0,hu1,hv0,hv1⟩

/-- The zero-angle endpoint cannot miss the border point with these two
strict witnesses. It is not discarded by a sign split. -/
theorem border_axial_forcing (q : OpenSquare) (t x y : ℝ)
    (hc : 0 ≤ q.c) (hs : q.s = 0) (hx : t ≤ x) (hy : y ≤ 1)
    (hbelow : q.Inside t y) (hright : q.Inside x 1) : q.Inside t 1 := by
  by_contra hmissing
  have hface := border_missing_positive_face q t x y hc (by rw [hs]) hx hy
    hbelow hright hmissing
  have hv := hright.2.2.2
  rw [hs] at hface hv
  nlinarith only [hface,hv]

/-- Upper-V exclusion expressed as a strict center inequality when the
true square side is greater than one. -/
theorem border_positive_center_bound (q : OpenSquare) (t : ℝ)
    (ha : 1 < q.side) (hface : q.loV+q.side ≤ -q.s*t+q.c) :
    1/2 < q.s*(centerX q-t)-q.c*(centerY q-1) := by
  have hcoord := (center_coordinates q).2
  nlinarith only [ha,hface,hcoord]

/-- Lower-U exclusion expressed as the strict opposite center bound. -/
theorem border_negative_center_bound (q : OpenSquare) (t : ℝ)
    (ha : 1 < q.side) (hface : q.c*t+q.s ≤ q.loU) :
    1/2 < q.c*(centerX q-t)+q.s*(centerY q-1) := by
  have hcoord := (center_coordinates q).1
  nlinarith only [ha,hface,hcoord]

/-- A point within the closed radius-one-half disk of the center is
strictly interior whenever the actual side exceeds one. -/
theorem border_center_disk_inside (q : OpenSquare) (x y : ℝ)
    (ha : 1 < q.side)
    (hd : (x-centerX q)^2+(y-centerY q)^2 ≤ 1/4) : q.Inside x y := by
  have hd' : (2*(x-centerX q))^2+(2*(y-centerY q))^2 ≤ 1 := by
    nlinarith only [hd]
  obtain ⟨u0,u1,v0,v1⟩ := short_projections q
    (2*(x-centerX q)) (2*(y-centerY q)) hd'
  obtain ⟨cu,cv⟩ := center_coordinates q
  change InBands q.loU q.loV q.side _ _
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [ha,u0,u1,v0,v1,cu,cv]

/-- Closed center-distance bounds are enough: two actual squares of side
greater than one with centers at distance at most one share the midpoint
strictly. Arbitrary orientations and equality at distance one are covered. -/
theorem border_close_centers_overlap (q r : OpenSquare)
    (haq : 1 < q.side) (har : 1 < r.side)
    (hd : (centerX r-centerX q)^2+(centerY r-centerY q)^2 ≤ 1) :
    ∃ x y : ℝ, q.Inside x y ∧ r.Inside x y := by
  refine ⟨(centerX q+centerX r)/2,(centerY q+centerY r)/2,?_,?_⟩
  · apply border_center_disk_inside q _ _ haq
    nlinarith only [hd]
  · apply border_center_disk_inside r _ _ har
    nlinarith only [hd]

/-- The pair contradiction used by the Euclidean-distance branch of the
border checker, directly against original packing disjointness. -/
theorem border_packing_center_distance (p : NormalizedPacking)
    (i j : Fin 12) (hij : i ≠ j) :
    1 < (centerX (p.square j)-centerX (p.square i))^2+
      (centerY (p.square j)-centerY (p.square i))^2 := by
  by_contra hh
  have hd := le_of_not_gt hh
  obtain ⟨x,y,hx,hy⟩ := border_close_centers_overlap (p.square i) (p.square j)
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_gt_one) hd
  exact p.disjoint i j hij x y ⟨hx,hy⟩

end S12Completion.C977

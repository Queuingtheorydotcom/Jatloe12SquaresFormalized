import Compact.Bridge.CongruentSAT
import Compact.Geometry.ThreeSquareSupport

/-!
The compulsory B/L triangles reduce the eight signed separating-axis
alternatives to three directed alternatives. This is an original-model
geometric reduction, not an assertion that B/L alone excludes a short B
section: an exact counterexample to that stronger claim is in the audit.
-/

namespace N12Compact.BLSeparation

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare C977ChainBridge

private theorem directed_support (q r : OpenSquare)
    (x y x' y' nx ny : ℝ)
    (hq : ClosedInside q x y) (hr : ClosedInside r x' y')
    (hp : nx * x + ny * y < nx * x' + ny * y') :
    nx * (centerX q - centerX r) + ny * (centerY q - centerY r) <
      supportRadius q nx ny + supportRadius r nx ny := by
  have hq' := (abs_le.mp (closed_support q x y nx ny hq)).1
  have hr' := (abs_le.mp (closed_support r x' y' nx ny hr)).2
  nlinarith only [hq', hr', hp]

private theorem parallel_radius (q r : OpenSquare) :
    supportRadius q q.c q.s + supportRadius r q.c q.s = pairRadius q r := by
  have hu : q.c * q.c + q.s * q.s = 1 := by nlinarith only [q.unit_normal]
  have hz : -q.c * q.s + q.s * q.c = 0 := by ring
  have hc : -q.c * r.s + q.s * r.c = -normalCross q r := by
    unfold normalCross
    ring
  simp only [supportRadius, hu, hz, abs_one, abs_zero, add_zero,
    mul_one, hc, abs_neg, pairRadius, normalDot]

private theorem perpendicular_radius (q r : OpenSquare) :
    supportRadius q (-q.s) q.c + supportRadius r (-q.s) q.c = pairRadius q r := by
  have hz : -q.s * q.c + q.c * q.s = 0 := by ring
  have hu : -(-q.s) * q.s + q.c * q.c = 1 := by nlinarith only [q.unit_normal]
  have hc : -q.s * r.c + q.c * r.s = normalCross q r := by
    unfold normalCross
    ring
  have hd : -(-q.s) * r.s + q.c * r.c = normalDot q r := by
    unfold normalDot
    ring
  simp only [supportRadius, hz, hu, abs_zero, abs_one, zero_add,
    mul_one, hc, hd, pairRadius]
  ring

/-- The B compulsory triangle and L compulsory triangle strictly overlap
on B's transverse projection. Weak contact on that separating axis is
therefore impossible, without assumptions about missing points or centers. -/
theorem transverse_overlap (B L : OpenSquare)
    (hc : 0 < B.c) (hs : 0 ≤ B.s) (hsc : B.s ≤ B.c)
    (bb : ClosedInside B (33 / 20) (47 / 20))
    (bt : ClosedInside B (8 / 5) 3)
    (ll : ClosedInside L (457 / 500) 2)
    (lt : ClosedInside L 1 (12 / 5)) :
    |-B.s * (centerX B - centerX L) + B.c * (centerY B - centerY L)| <
      pairRadius B L := by
  apply abs_lt.mpr
  constructor
  · have h := directed_support L B (457 / 500) 2 (8 / 5) 3 (-B.s) B.c ll bt
      (by nlinarith only [hc, hs, hsc])
    rw [add_comm (supportRadius L (-B.s) B.c) (supportRadius B (-B.s) B.c),
      perpendicular_radius] at h
    nlinarith only [h]
  · have h := directed_support B L (33 / 20) (47 / 20) 1 (12 / 5)
      (-B.s) B.c bb lt (by nlinarith only [hc, hs])
    rwa [perpendicular_radius] at h

/-- A positive canonical B can lie only to the right of L on either
longitudinal separating axis. The only other possible axis is L's
transverse axis, and it forces the explicit negative-slope bound
`13 * L.s ≤ -L.c`. No branch count depends on angle resolution. -/
theorem three_directed_alternatives (B L : OpenSquare)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (bb : ClosedInside B (33 / 20) (47 / 20))
    (bt : ClosedInside B (8 / 5) 3)
    (ll : ClosedInside L (457 / 500) 2)
    (lt : ClosedInside L 1 (12 / 5))
    (same : B.side = L.side)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y)) :
    pairRadius B L ≤
        B.c * (centerX B - centerX L) + B.s * (centerY B - centerY L) ∨
    pairRadius L B ≤
        L.c * (centerX B - centerX L) + L.s * (centerY B - centerY L) ∨
    (13 * L.s ≤ -L.c ∧
      pairRadius L B ≤
        -L.s * (centerX B - centerX L) + L.c * (centerY B - centerY L)) := by
  have lsb := abs_le.mp lsc
  have bu_backward :
      -(B.c * (centerX B - centerX L) + B.s * (centerY B - centerY L)) <
        pairRadius B L := by
    have h := directed_support L B (457 / 500) 2 (8 / 5) 3 B.c B.s ll bt
      (by nlinarith only [bc, bs])
    rw [add_comm (supportRadius L B.c B.s) (supportRadius B B.c B.s),
      parallel_radius] at h
    nlinarith only [h]
  have lu_backward :
      -(L.c * (centerX B - centerX L) + L.s * (centerY B - centerY L)) <
        pairRadius L B := by
    have h := directed_support L B 1 (12 / 5) (33 / 20) (47 / 20)
      L.c L.s lt bb (by nlinarith only [lc, lsb.2])
    rw [parallel_radius] at h
    nlinarith only [h]
  have lv_backward :
      -(-L.s * (centerX B - centerX L) + L.c * (centerY B - centerY L)) <
        pairRadius L B := by
    have h := directed_support L B (457 / 500) 2 (8 / 5) 3 (-L.s) L.c ll bt
      (by nlinarith only [lc, lsb.2])
    rw [perpendicular_radius] at h
    nlinarith only [h]
  have orient (x R : ℝ) (hb : -x < R) (h : R ≤ |x|) : R ≤ x := by
    by_cases hx : 0 ≤ x
    · simpa only [abs_of_nonneg hx] using h
    · have hh : R ≤ -x := by
        simpa only [abs_of_nonpos (le_of_not_ge hx)] using h
      exact False.elim ((not_le_of_gt hb) hh)
  have hs := CongruentSAT.faceSeparation_of_disjoint B L same apart
  change pairRadius B L ≤ |B.c * (centerX L - centerX B) +
      B.s * (centerY L - centerY B)| ∨
    pairRadius B L ≤ |-B.s * (centerX L - centerX B) +
      B.c * (centerY L - centerY B)| ∨
    pairRadius L B ≤ |L.c * (centerX L - centerX B) +
      L.s * (centerY L - centerY B)| ∨
    pairRadius L B ≤ |-L.s * (centerX L - centerX B) +
      L.c * (centerY L - centerY B)| at hs
  have reverse (nx ny : ℝ) :
      |nx * (centerX L - centerX B) + ny * (centerY L - centerY B)| =
      |nx * (centerX B - centerX L) + ny * (centerY B - centerY L)| := by
    have he : nx * (centerX L - centerX B) + ny * (centerY L - centerY B) =
        -(nx * (centerX B - centerX L) + ny * (centerY B - centerY L)) := by ring
    rw [he, abs_neg]
  rcases hs with hu | hv | hu | hv
  · exact Or.inl (orient _ _ bu_backward (by rwa [reverse] at hu))
  · rw [reverse] at hv
    exact False.elim ((not_le_of_gt (transverse_overlap B L bc bs bsc bb bt ll lt)) hv)
  · exact Or.inr (Or.inl (orient _ _ lu_backward (by rwa [reverse] at hu)))
  · rw [reverse] at hv
    have hf := orient _ _ lv_backward hv
    apply Or.inr
    apply Or.inr
    refine ⟨?_, hf⟩
    by_contra hn
    have hslope : -L.c < 13 * L.s := lt_of_not_ge hn
    have h := directed_support B L (33 / 20) (47 / 20) 1 (12 / 5)
      (-L.s) L.c bb lt (by nlinarith only [hslope])
    rw [add_comm (supportRadius B (-L.s) L.c) (supportRadius L (-L.s) L.c),
      perpendicular_radius] at h
    linarith only [h, hf]

end N12Compact.BLSeparation

import Completion.Cases.C977.WallBranches

namespace S12Completion.C977
open S12 S12Pilot

/-- A point outside an open square lies outside its centered open disk of
    radius half the side. The conclusion is closed, so boundary contact is
    retained. The normal may have any signs or include an axis direction. -/
theorem outside_center_distance (q : OpenSquare) (x y : ℝ)
    (hout : ¬q.Inside x y) :
    q.side ^ 2 / 4 ≤ (x - centerX q) ^ 2 + (y - centerY q) ^ 2 := by
  let du := q.c * (x - centerX q) + q.s * (y - centerY q)
  let dv := -q.s * (x - centerX q) + q.c * (y - centerY q)
  have hrot : du ^ 2 + dv ^ 2 =
      (x - centerX q) ^ 2 + (y - centerY q) ^ 2 := by
    calc
      _ = (q.c ^ 2 + q.s ^ 2) *
          ((x - centerX q) ^ 2 + (y - centerY q) ^ 2) := by dsimp [du, dv]; ring
      _ = _ := by rw [q.unit_normal, one_mul]
  have hband : ¬InBands (-q.side / 2) (-q.side / 2) q.side du dv := by
    intro hi
    exact hout ((inside_centered_iff q x y).mpr hi)
  simp only [InBands, not_and_or, not_lt] at hband
  rw [← hrot]
  rcases hband with h | h | h | h
  · have hp := mul_nonneg
      (show 0 ≤ -du - q.side / 2 by linarith only [h])
      (show 0 ≤ -du + q.side / 2 by linarith only [h, q.side_pos])
    nlinarith only [hp, sq_nonneg dv]
  · have hp := mul_nonneg
      (show 0 ≤ du - q.side / 2 by linarith only [h])
      (show 0 ≤ du + q.side / 2 by linarith only [h, q.side_pos])
    nlinarith only [hp, sq_nonneg dv]
  · have hp := mul_nonneg
      (show 0 ≤ -dv - q.side / 2 by linarith only [h])
      (show 0 ≤ -dv + q.side / 2 by linarith only [h, q.side_pos])
    nlinarith only [hp, sq_nonneg du]
  · have hp := mul_nonneg
      (show 0 ≤ dv - q.side / 2 by linarith only [h])
      (show 0 ≤ dv + q.side / 2 by linarith only [h, q.side_pos])
    nlinarith only [hp, sq_nonneg du]

/-- The unused central marker excludes a disk from the center of every
    original square, with the actual common side retained. -/
theorem unused_marker_center_distance (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    p.commonSide ^ 2 / 4 ≤
      (47 / 20 - centerX (p.square i)) ^ 2 +
      (47 / 20 - centerY (p.square i)) ^ 2 := by
  have hout : ¬(p.square i).Inside (47 / 20) (47 / 20) := by
    simpa [Owns, marker] using unused_marker_ten p hf i
  have hd := outside_center_distance (p.square i) (47 / 20) (47 / 20) hout
  simpa only [p.congruent] using hd

/-- The disk of radius one half is strictly excluded because the common
    side is strictly greater than one, even at a square boundary contact. -/
theorem unused_marker_center_distance_strict (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    1 / 4 < (47 / 20 - centerX (p.square i)) ^ 2 +
      (47 / 20 - centerY (p.square i)) ^ 2 := by
  have hd := unused_marker_center_distance p hf i
  have hp := mul_pos
    (show 0 < p.commonSide - 1 by linarith only [p.side_gt_one])
    (show 0 < p.commonSide + 1 by linarith only [p.side_gt_one])
  nlinarith only [hd, hp]

end S12Completion.C977

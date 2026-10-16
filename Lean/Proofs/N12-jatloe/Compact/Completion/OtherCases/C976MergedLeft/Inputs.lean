import Compact.Completion.OtherCases.C976LeftTop.PointSign

/-! Literal physical inputs of C976-MERGED-LEFT-ENDING Theorem 1.
The northwest marker belongs to the merged C976 square; there is no
corresponding C974 premise. Both foreign segments include their ends. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1<q.side
  left : q.Inside (-(43/500)) 0
  marker : q.Inside (13/20) (7/20)
  inward : q.Inside 0 (13/50)
  middle : ¬q.Inside (1/2) 0
  corner : ¬q.Inside 0 1
  top : ∀ x : ℝ,27/100≤x → x≤37/50 → ¬q.Inside x 1
  segment : ∀ t : ℝ,0≤t → t≤1 →
    ¬q.Inside (-6/25+(6/25)*t) (-13/100-(13/100)*t)

theorem Input.reframe {q r : OpenSquare} (h : Input q)
    (side : r.side=q.side) (inside : ∀ x y,r.Inside x y↔q.Inside x y) : Input r where
  side := by simpa only [side] using h.side
  left := (inside _ _).mpr h.left
  marker := (inside _ _).mpr h.marker
  inward := (inside _ _).mpr h.inward
  middle := fun p => h.middle ((inside _ _).mp p)
  corner := fun p => h.corner ((inside _ _).mp p)
  top := fun x lo hi p => h.top x lo hi ((inside _ _).mp p)
  segment := fun t lo hi p => h.segment t lo hi ((inside _ _).mp p)

/-- The older nonpositive proof has exactly the same anchors and lower
segment. Its missing-target premise is introduced only by contradiction. -/
theorem Input.with_missing_target {q : OpenSquare} (h : Input q)
    (missing : ¬q.Inside (27/100) (-(1/25))) : C976LeftTop.UpperPoints.Input q where
  side := h.side
  left := h.left
  marker := h.marker
  inward := h.inward
  middle := h.middle
  corner := h.corner
  lower := missing
  top := fun x lo hi => h.top x (by linarith only [lo]) hi
  segment := h.segment

structure Profile (q : OpenSquare) : Prop where
  cosine : 0<q.c
  sine : 0<q.s
  canonical : q.s≤q.c
  angleLower : (38/65)*q.c<q.s
  lowerV : -(1/2)*q.s≤q.loV
  upperV : q.loV+q.side≤q.c
  upperU : q.loU+q.side≤(27/100)*q.c+q.s

end N12Compact.Completion.OtherCases.C976MergedLeft

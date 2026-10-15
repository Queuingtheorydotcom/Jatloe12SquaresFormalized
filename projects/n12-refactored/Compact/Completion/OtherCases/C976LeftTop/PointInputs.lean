import Compact.Geometry.ClosedFrames
import Compact.Geometry.SegmentCorner
import Compact.Completion.CommonCases.OutwardScalars

/-! Literal inputs of C976-LEFT-UPPER-POINTS. Both omitted segments are
whole closed parameter intervals; no support inequality replaces either. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1<q.side
  left : q.Inside (-(43/500)) 0
  marker : q.Inside (13/20) (7/20)
  inward : q.Inside 0 (13/50)
  middle : ¬q.Inside (1/2) 0
  corner : ¬q.Inside 0 1
  lower : ¬q.Inside (27/100) (-(1/25))
  top : ∀ x : ℝ,11/25≤x → x≤37/50 → ¬q.Inside x 1
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
  lower := fun p => h.lower ((inside _ _).mp p)
  top := fun x lo hi p => h.top x lo hi ((inside _ _).mp p)
  segment := fun t lo hi p => h.segment t lo hi ((inside _ _).mp p)

structure Profile (q : OpenSquare) : Prop where
  cosine : 0<q.c
  sine : 0<q.s
  canonical : q.s≤q.c
  angleLower : (21/65)*q.c<q.s
  angleUpper : q.s<(3/4)*q.c
  lowerV : -(27/100)*q.s-(1/25)*q.c≤q.loV
  upperV : q.loV+q.side≤q.c
  upperU : q.loU+q.side≤(11/25)*q.c+q.s

end N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints

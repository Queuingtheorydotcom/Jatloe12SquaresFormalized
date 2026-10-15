import Compact.Geometry.ClosedFrames
import Compact.Completion.CommonCases.CanonicalScalars

/-! Literal hypotheses of ORDINARY-LEFT-TOP-OBSTRUCTION.md, Theorem 1.
The seven absences remain individual absences, with no common foreign owner
or wall assumption. This is a source translation, not a replay receipt. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1 < q.side
  marker : q.Inside (13/20) (7/20)
  anchor : q.Inside 0 (13/50)
  left : ¬ q.Inside (-(43/500)) 0
  middle : ¬ q.Inside (1/2) 0
  far : ¬ q.Inside (37/50) 0
  corner : ¬ q.Inside 0 1
  lower : ¬ q.Inside (27/100) (-(1/25))
  topNear : ¬ q.Inside (11/25) 1
  topFar : ¬ q.Inside (37/50) 1

theorem Input.reframe {q r : OpenSquare} (h : Input q)
    (side : r.side = q.side) (inside : ∀ x y, r.Inside x y ↔ q.Inside x y) :
    Input r where
  side := by simpa only [side] using h.side
  marker := (inside _ _).mpr h.marker
  anchor := (inside _ _).mpr h.anchor
  left := fun own => h.left ((inside _ _).mp own)
  middle := fun own => h.middle ((inside _ _).mp own)
  far := fun own => h.far ((inside _ _).mp own)
  corner := fun own => h.corner ((inside _ _).mp own)
  lower := fun own => h.lower ((inside _ _).mp own)
  topNear := fun own => h.topNear ((inside _ _).mp own)
  topFar := fun own => h.topFar ((inside _ _).mp own)

end N12Compact.Completion.OtherCases.OrdinaryLeftTop

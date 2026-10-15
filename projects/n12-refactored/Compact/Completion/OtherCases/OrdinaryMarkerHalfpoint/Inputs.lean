import Compact.Geometry.ClosedFrames
import S12.ShortCluster.Projections

/-! Literal parameterized hypotheses of ORDINARY-MARKER-HALFPOINT.
The foreign wall marker is allowed anywhere in its full stated interval. -/
namespace N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) (d : ℝ) : Prop where
  side : 1<q.side
  offsetNonnegative : 0≤d
  offsetUpper : d≤13/50
  marker : q.Inside (7/20) (-7/20)
  near : q.Inside 1 (-13/50)
  far : q.Inside 1 (-2/5)
  missingInward : ¬q.Inside (13/50) 0
  missingRight : ¬q.Inside (1+d) 0
  missingCorner : ¬q.Inside 1 (-1)
  missingLower : ¬q.Inside (13/50) (-1)

theorem Input.reframe {q r : OpenSquare} {d : ℝ} (h : Input q d)
    (side : r.side=q.side) (same : ∀ x y,r.Inside x y ↔ q.Inside x y) : Input r d where
  side := by simpa only [side] using h.side
  offsetNonnegative := h.offsetNonnegative
  offsetUpper := h.offsetUpper
  marker := (same _ _).mpr h.marker
  near := (same _ _).mpr h.near
  far := (same _ _).mpr h.far
  missingInward := fun own => h.missingInward ((same _ _).mp own)
  missingRight := fun own => h.missingRight ((same _ _).mp own)
  missingCorner := fun own => h.missingCorner ((same _ _).mp own)
  missingLower := fun own => h.missingLower ((same _ _).mp own)

end N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint

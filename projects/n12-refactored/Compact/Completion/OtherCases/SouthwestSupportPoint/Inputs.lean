import Compact.Geometry.ClosedFrames
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Completion.OtherCases.LowerCornerSupport
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Completion.CommonCases.CanonicalProjection

/-! Literal centered premises of C974-C976-SW-SUPPORT-POINT Theorem 1.
The bottom and southeast segments are separate exclusions. No ownership
relation between them is asserted or needed. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint
open S12 S12Pilot
set_option Elab.async false

structure Input (q : OpenSquare) : Prop where
  side : 1<q.side
  marker : q.Inside (-7/20) (-7/20)
  inwardSouth : q.Inside 0 (-13/50)
  inwardWest : q.Inside (-13/50) 0
  west : q.Inside (-1/2) 0
  south : q.Inside 0 (-1/2)
  missingNorth : ¬q.Inside (-7/20) (7/20)
  missingEast : ¬q.Inside (7/20) (-7/20)
  missingBottom : ¬q.Inside 0 (-1)
  missingLeftLow : ¬q.Inside (-1) (-2/5)
  missingLeftHigh : ¬q.Inside (-1) (-13/50)
  bottomSegment : ∀ x : ℝ,-1/2≤x → x≤ -13/50 → ¬q.Inside x (-1)
  southeastSegment : ∀ t : ℝ,0≤t → t≤1 →
    ¬q.Inside (7/20-(9/100)*t) (-7/20+(7/20)*t)

theorem Input.reframe {q r : OpenSquare} (h : Input q) (side : r.side=q.side)
    (same : ∀ x y,r.Inside x y ↔ q.Inside x y) : Input r where
  side := by simpa only [side] using h.side
  marker := (same _ _).mpr h.marker
  inwardSouth := (same _ _).mpr h.inwardSouth
  inwardWest := (same _ _).mpr h.inwardWest
  west := (same _ _).mpr h.west
  south := (same _ _).mpr h.south
  missingNorth := fun p => h.missingNorth ((same _ _).mp p)
  missingEast := fun p => h.missingEast ((same _ _).mp p)
  missingBottom := fun p => h.missingBottom ((same _ _).mp p)
  missingLeftLow := fun p => h.missingLeftLow ((same _ _).mp p)
  missingLeftHigh := fun p => h.missingLeftHigh ((same _ _).mp p)
  bottomSegment := fun x low high p => h.bottomSegment x low high ((same _ _).mp p)
  southeastSegment := fun t low high p => h.southeastSegment t low high ((same _ _).mp p)

end N12Compact.Completion.OtherCases.SouthwestSupportPoint

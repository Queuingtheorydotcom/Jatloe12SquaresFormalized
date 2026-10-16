import Compact.Geometry.C977CornerCubic
import S12.Diagonal

/-! Exact faces of the negative upper-merged frame in coordinates
centered at (2,2). Both original upper markers and every actual omitted
point remain explicit. The last point lemma is deliberately conditional
on its displayed scalar inequality: it does not discard the steep end
or replace separation from the actual southeast square by a point hull. -/
namespace N12Compact.MergedPending.NegativeUpperFaces
open S12Pilot C977CornerCubic
set_option Elab.async false

structure Input (H : OpenSquare) : Prop where
  normal : Normal H.c (-H.s)
  side : 1<H.side
  northwest : H.Inside (-7/20) (7/20)
  northeast : H.Inside (7/20) (7/20)
  missingWest : ¬H.Inside (-13/50) 0
  missingTopLeft : ¬H.Inside (-13/50) 1
  missingTopMarker : ¬H.Inside 0 (543/500)

/-- Foreign southwest G3 forces the lower V face. -/
theorem lower_v (H : OpenSquare) (h : Input H) : (13/50)*H.s≤H.loV := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  apply le_of_not_gt
  intro low
  apply h.missingWest
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.northwest.1,cp,h.normal.1]
  · linarith only [h.northeast.2.1,cp,h.normal.2.1]
  · linarith only [low]
  · linarith only [h.northwest.2.2.2,cp,h.normal.2.1]

/-- The actual top G4 cannot leave through either V face; its lower U
exit is therefore forced, including every tangent contact. -/
theorem lower_u (H : OpenSquare) (h : Input H) :
    -(13/50)*H.c+H.s≤H.loU := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have floor := lower_v H h
  apply le_of_not_gt
  intro low
  apply h.missingTopLeft
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [low]
  · linarith only [h.northeast.2.1,cp,h.normal.1]
  · linarith only [h.northeast.2.2.1,cp,h.normal.2.1]
  · linarith only [floor,h.side,bounds.2.1]

theorem tilt (H : OpenSquare) (h : Input H) : 9*H.c< -65*H.s := by
  have floor := lower_u H h
  linarith only [floor,h.northwest.1]

/-- Unlike an assumed cap, this disjunction comes from the actual top
owner's marker. Both possible remaining exits are retained. -/
theorem top_marker_faces (H : OpenSquare) (h : Input H) :
    (543/500)*H.s≤H.loU ∨ H.loV+H.side≤(543/500)*H.c := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  by_cases low : (543/500)*H.s≤H.loU
  · exact Or.inl low
  · right
    apply le_of_not_gt
    intro high
    apply h.missingTopMarker
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [low]
    · linarith only [h.northeast.2.1,cp,h.normal.1]
    · linarith only [h.northeast.2.2.1,cp,h.normal.2.1]
    · linarith only [high]

theorem top_lower_tilt (H : OpenSquare) (h : Input H)
    (floor : (543/500)*H.s≤H.loU) : 175*H.c< -368*H.s := by
  linarith only [floor,h.northwest.1]

/-- The genuine outward-SE point (2.525,2.125), in this translated
chart, is strict in H on the indicated closed scalar region. When an
actual disjoint SE owner supplies it, this region is impossible. -/
theorem sharp_point (H : OpenSquare) (h : Input H)
    (floor : (543/500)*H.s≤H.loU)
    (lowerAngle : 9*H.c≤ -35*H.s)
    (upperProjection : 525*H.c-961*H.s≤1000) :
    H.Inside (21/40) (1/8) := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have vfloor := lower_v H h
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.northeast.1,cp,h.normal.1]
  · linarith only [floor,h.side,upperProjection]
  · linarith only [h.northwest.2.2.1,lowerAngle]
  · linarith only [vfloor,h.side,bounds.2.1,bounds.2.2.2.1]

#print axioms lower_v
#print axioms lower_u
#print axioms tilt
#print axioms top_marker_faces
#print axioms sharp_point
end N12Compact.MergedPending.NegativeUpperFaces

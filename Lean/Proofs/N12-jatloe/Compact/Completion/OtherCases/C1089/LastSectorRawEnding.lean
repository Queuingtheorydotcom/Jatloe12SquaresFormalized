import Compact.Completion.OtherCases.C1089.LastSectorRawPoints
import Compact.Completion.OtherCases.C1089.LastSectorEnding

/-! A compact join of the actual last-sector producers to the eight-point
ending. The raw finite core, the indicated auxiliary pairs and conditional
stronger singleton seeds remain genuine entrance obligations. Derived center,
crosspoints, singleton corner, northwest pair, origins and advances are not
assumed. This source does not assert a complete ExcludesCase1089 theorem. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorRawPoints
open S12 S12Pilot
set_option Elab.async false

theorem ending_input (q : Fin 12 → OpenSquare) (h : Input q) : LastSectorEnding.Input q := by
  have a := southwest_pair q h
  have n := northwest_pair q h
  exact {
    side := h.side
    same := h.same
    contained := h.contained
    apart := h.apart
    singletonCorner := singleton_corner q h
    singletonNear := h.singletonNear
    singletonFar := h.singletonFar
    absentMarker := h.absentMarker
    southeastCornerMarker := h.southeastCornerMarker
    southeastCorner := h.southeastCorner
    northeastCornerMarker := h.northeastCornerMarker
    northeastCorner := h.northeastCorner
    northwestCorner := h.northwestCorner
    southwestMarker := h.southwestMarker
    southwestF0 := a.1
    southwestG0 := a.2
    southeastMarker := h.southeastMarker
    southeastF4 := h.southeastF4
    southeastG6 := h.southeastG6
    southeastEast := southeast_east q h
    southeastSouth := southeast_south q h
    northeastMarker := h.northeastMarker
    northeastF9 := h.northeastF9
    northeastG9 := h.northeastG9
    northwestMarker := h.northwestMarker
    northwestF3 := n.1
    northwestG4 := n.2
    leftMarker := h.leftMarker
    leftF1 := h.leftF1
    leftG1 := h.leftG1
    bottomMarker := h.bottomMarker
    bottomF6 := h.bottomF6
    bottomG5 := h.bottomG5
    bottomAdvance := bottom_advance q h
    rightMarker := h.rightMarker
    rightG8 := h.rightG8
    rightOrigin := (southeast_center_and_right_origin q h).2
    topMarker := h.topMarker
    topF7 := h.topF7
    topG7 := h.topG7 }

theorem impossible (q : Fin 12 → OpenSquare) (h : Input q) : False :=
  LastSectorEnding.impossible q (ending_input q h)

#print axioms ending_input
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.LastSectorRawPoints

import Compact.Completion.OtherCases.C1089.LastSectorExtra
import Compact.Completion.OtherCases.C1089.WallOrigins

/-! A source-level geometric ending for the final C1089 sector. The
actual point table here precedes the new wall-origin, wall-advance and
southwest-extra consequences; each of these is derived in this module.
The earlier auxiliary/center/crosspoint entrance and the singleton inner
corner are still required original-owner inputs. This is not ExcludesCase1089.
No compiler or whole-case acceptance is asserted. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorEnding
open S12 S12Pilot
set_option Elab.async false

structure Input (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  same : ∀ i j,(q i).side=(q j).side
  contained : ∀ i,InsideContainer (q i)
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  singletonCorner : (q 0).Inside 1 1
  singletonNear : (q 0).Inside (28/25) 1
  singletonFar : (q 0).Inside (87/50) 1
  absentMarker : ∀ i,¬(q i).Inside (457/500) 1
  southeastCornerMarker : (q 1).Inside 3 (457/500)
  southeastCorner : (q 1).Inside 3 1
  northeastCornerMarker : (q 2).Inside 3 (1543/500)
  northeastCorner : (q 2).Inside 3 3
  northwestCorner : (q 3).Inside 1 3
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southwestF0 : (q 4).Inside 1 (87/50)
  southwestG0 : (q 4).Inside 1 (8/5)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  southeastF4 : (q 5).Inside 2 (87/50)
  southeastG6 : (q 5).Inside (113/50) 2
  southeastEast : (q 5).Inside (5/2) 2
  southeastSouth : (q 5).Inside 2 (3/2)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northeastF9 : (q 6).Inside 3 (113/50)
  northeastG9 : (q 6).Inside 3 (12/5)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  northwestF3 : (q 7).Inside (8/5) 3
  northwestG4 : (q 7).Inside (87/50) 3
  leftMarker : (q 8).Inside (457/500) 2
  leftF1 : (q 8).Inside 1 (113/50)
  leftG1 : (q 8).Inside 1 (12/5)
  bottomMarker : (q 9).Inside 2 (457/500)
  bottomF6 : (q 9).Inside (12/5) 1
  bottomG5 : (q 9).Inside (113/50) 1
  bottomAdvance : (q 9).Inside (14/5) 1
  rightMarker : (q 10).Inside (1543/500) 2
  rightG8 : (q 10).Inside 3 (8/5)
  rightOrigin : (q 10).Inside 3 2
  topMarker : (q 11).Inside 2 (1543/500)
  topF7 : (q 11).Inside (12/5) 3
  topG7 : (q 11).Inside (113/50) 3

theorem reduced_input (q : Fin 12 → OpenSquare) (h : Input q) : LastSectorExtra.Input q := by
  have left := WallOrigins.left_advance q (h.side 8) (h.contained 8) h.apart
    h.leftMarker h.leftG1 h.southwestF0 h.northwestMarker
  have right := WallOrigins.right_low q (h.side 10) (h.contained 10) h.apart
    h.rightMarker h.rightG8 h.northeastF9 h.southeastMarker
  have bottom := WallOrigins.bottom_origin q (h.side 9) (h.same 9 1) h.contained h.apart
    h.bottomMarker h.bottomF6 h.southeastCornerMarker h.southeastCorner right h.rightG8
  have top := WallOrigins.top_origin_of_ordinary q h.side h.same h.contained h.apart
    h.northeastMarker h.northeastF9 h.northeastG9 h.southeastG6 h.rightMarker h.topG7
    h.topMarker h.topF7 h.northeastCornerMarker h.northeastCorner
  have advance := WallOrigins.top_advance q (h.side 11) (h.contained 11) h.apart
    h.topMarker h.topF7 h.northwestG4 h.northeastMarker
  exact {
    side := h.side
    apart := h.apart
    southwestMarker := h.southwestMarker
    southeastMarker := h.southeastMarker
    southeastF4 := h.southeastF4
    southeastG6 := h.southeastG6
    southeastEast := h.southeastEast
    southeastSouth := h.southeastSouth
    northeastMarker := h.northeastMarker
    northeastF9 := h.northeastF9
    rightLow := right
    rightOrigin := h.rightOrigin
    bottomOrigin := bottom
    bottomNear := h.bottomG5
    bottomAdvance := h.bottomAdvance
    topOrigin := top
    topAdvance := advance
    northeastCorner := h.northeastCorner
    sameSouthwestNorthwest := h.same 4 7
    southwestF0 := h.southwestF0
    southwestG0 := h.southwestG0
    singletonCorner := h.singletonCorner
    singletonNear := h.singletonNear
    singletonFar := h.singletonFar
    absentMarker := h.absentMarker
    leftMarker := h.leftMarker
    leftNear := h.leftF1
    leftFar := left
    northwestMarker := h.northwestMarker
    northwestF3 := h.northwestF3
    northwestG4 := h.northwestG4
    northwestCorner := h.northwestCorner }

/-- Every post-reduction actual point table above is contradictory;
the new origins, advances, extra auxiliary and support point are proved. -/
theorem impossible (q : Fin 12 → OpenSquare) (h : Input q) : False :=
  LastSectorExtra.impossible q (reduced_input q h)

#print axioms reduced_input
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.LastSectorEnding

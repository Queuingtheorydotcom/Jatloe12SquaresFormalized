import Compact.Completion.OtherCases.C1090.EarlySelection
import Compact.Completion.OtherCases.C1090.ResidualEnding

/-! The honest boundary between C1090's early reductions and its final
continuous ending. The later central structural eliminations must still
produce S's G6 and E's F7; neither conclusion is asserted by Early.Input.
Once supplied, every other residual premise is proved from the early raw
table. This is not a finite entrance or ExcludesCase theorem. Uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.Early
open S12 S12Pilot
set_option Elab.async false

theorem residual_input (q : Fin 12 → OpenSquare) (h : PointTable q)
    (southeastG6 : (q 5).Inside (113/50) 2)
    (northeastF7 : (q 6).Inside (12/5) 3) : Residual.Input q where
  side := h.side
  same := h.same
  box := h.box
  apart := h.apart
  singletonNear := h.singletonNear
  singletonFar := h.singletonFar
  southeastCornerMarker := h.southeastCornerBottom
  southeastCorner := h.southeastCorner
  northeastCorner := h.northeastCorner
  northwestCornerMarker := h.northwestCornerMarker
  northwestCorner := h.northwestCorner
  southwestMarker := h.southwestMarker
  southwestF4 := h.southwestF4
  southwestG3 := h.southwestG3
  southwestWest := h.southwestWest
  southwestSouth := h.southwestSouth
  southeastMarker := h.southeastMarker
  southeastF8 := h.southeastF8
  southeastG6 := southeastG6
  southeastG8 := h.southeastG8
  northeastMarker := h.northeastMarker
  northeastF7 := northeastF7
  northeastG7 := h.northeastG7
  northwestMarker := h.northwestMarker
  northwestF1 := h.northwestF1
  northwestG1 := h.northwestG1
  leftMarker := h.mergedMarker12
  leftF0 := h.leftBar _ (by norm_num) (by norm_num)
  leftG0 := h.leftBar _ (by norm_num) (by norm_num)
  bottomMarker := h.bottomMarker
  bottomF6 := h.bottomF6
  bottomG5 := h.bottomG5
  bottomAdvance := h.bottomAdvance
  rightF9 := h.rightF9
  rightAdvance := h.rightAdvance
  topMarker := h.topMarker
  topF3 := h.topF3
  topG4 := h.topG4

theorem residual_impossible (q : Fin 12 → OpenSquare) (h : Input q)
    (southeastG6 : (q 5).Inside (113/50) 2)
    (northeastF7 : (q 6).Inside (12/5) 3) : False :=
  Residual.impossible q (residual_input q (point_table q h) southeastG6 northeastF7)

#print axioms residual_input
#print axioms residual_impossible
end N12Compact.Completion.OtherCases.C1090.Early

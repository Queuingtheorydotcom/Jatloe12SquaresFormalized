import Compact.Completion.OtherCases.C976.EarlyGeometry
import Compact.Completion.OtherCases.C976.ResidualEnding
import Compact.Completion.CommonCases.C974976Origins
import Compact.Completion.OtherCases.F4PointTransfers

/-! The actual C976 family supplies every field of its continuous
ending. Top origin is derived before southeast G6, using the same merged
left6144 and paired northwest192; bottom origin then uses the actual
southeast12 corner and derived central512 lower point. No origin, angle,
support bound, exact auxiliary label or finite entrance is assumed. -/
namespace N12Compact.Completion.OtherCases.C976.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside 2 3 := by
  have h := fixed p hf
  exact CommonCases.C974976Central.top_origin _ _ _ (side p 8) (side p 11)
    (same p 11 4) (box p 8) (box p 11) (box p 4) h.leftMarker h.leftG1
    (foreign p hf 8 1 (by decide) _ _ (singleton_vertical p hf _ (by norm_num) le_rfl))
    (foreign p hf 8 5 (by decide) _ _ h.southwestG3)
    h.topMarker (top_pair p hf).1 h.northwestCornerMarker h.northwestCorner
    (apart p hf 4 8 (by decide)) (apart p hf 4 11 (by decide))

theorem ending_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    CommonCases.C974976Central.EndingInput (owners p 6) (owners p 7) where
  toInput := selection_input p hf
  topOrigin := foreign p hf 7 11 (by decide) _ _ (top_origin p hf)
  northeastCorner := foreign p hf 7 3 (by decide) _ _ (fixed p hf).northeastCorner
  rightBar := fun y low high => foreign p hf 7 10 (by decide) _ _ (right_bar p hf y low high)

theorem southeast_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (113/50) 2 :=
  CommonCases.C974976Central.southeast_g6 _ _ (ending_input p hf)

theorem southeast_east (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (5/2) 2 := by
  have h := fixed p hf
  exact F4PointTransfers.horizontal_original (owners p 6) (side p 6)
    h.southeastMarker (southeast_g6 p hf) h.southeastF8
    (foreign p hf 6 5 (by decide) _ _ h.southwestF4)
    (foreign p hf 6 9 (by decide) _ _ ((bottom_reach p hf).2 _ (by norm_num) (by norm_num)))

theorem southeast_lower (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 3 (3/2) :=
  CommonCases.C974976Central.southeast_lower _ _ (ending_input p hf) (southeast_g6 p hf)

theorem bottom_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside 2 1 := by
  have h := fixed p hf
  exact CommonCases.C974976Central.bottom_origin _ _ _ (side p 9) (same p 9 2)
    (box p 9) (box p 2) h.bottomMarker h.bottomF6 h.southeastCornerBottom h.southeastCorner
    (southeast_lower p hf) (apart p hf 2 6 (by decide)) (apart p hf 2 9 (by decide))

theorem actual_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    C976.Data (owners p) := by
  have h := fixed p hf
  exact {
    side := side p
    same := same p
    box := box p
    apart := apart p hf
    singleton0First := singleton_horizontal p hf _ le_rfl (by norm_num)
    singleton0Last := singleton_horizontal p hf _ (by norm_num) le_rfl
    singleton1Low := singleton_vertical p hf _ (by norm_num) (by norm_num)
    singleton1Near := singleton_vertical p hf _ (by norm_num) le_rfl
    singleton1Seed := h.singleton1Seed
    cornerMarker := h.northwestCornerMarker
    cornerPoint := h.northwestCorner
    southwestMarker := h.southwestMarker
    southwestF4 := h.southwestF4
    southwestG3 := h.southwestG3
    southwestWest := southwest_west p hf
    southwestSouth := southwest_south p hf
    southeastMarker := h.southeastMarker
    southeastG6 := southeast_g6 p hf
    northeastG7 := northeast_g7 p hf
    leftMarker := h.leftMarker
    northwestMarker := h.northwestMarker
    leftF1 := h.leftF1
    bottomOrigin := bottom_origin p hf
    topMarker := h.topMarker
    topF3 := (top_pair p hf).1
    topG4 := (top_pair p hf).2
    northeastMarker := h.northeastMarker
    northeastF7 := northeast_f7 p hf
    northeastCorner := h.northeastCorner
    southeastF8 := h.southeastF8
    southeastEast := southeast_east p hf
    rightMarker := h.rightMarker
    rightF9 := h.rightF9
    rightG9 := h.rightG9 }

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False :=
  C976.impossible (owners p) (actual_data p hf)

end
#print axioms top_origin
#print axioms actual_data
#print axioms impossible
end N12Compact.Completion.OtherCases.C976.OriginalData

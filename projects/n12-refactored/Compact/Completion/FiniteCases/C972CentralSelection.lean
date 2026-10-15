import Compact.Completion.FiniteCases.C972Entrance
import Compact.Completion.CommonCases.C974976Central
import Compact.Completion.C981.Crosspoint
import Compact.Completion.OtherCases.C1089.ContinuousBottom
import Compact.Geometry.WallUpperMissingReach

/-! C972's continuous central selection. The southwest crosspoints and
actual bottom bar force SE G8 and NE F7/G7. Those genuine foreign points
then force NW G4; its elbow alternative would duplicate the southwest
crosspoint, so NW also owns F3. Marker 15 is an omission, never a top owner. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
set_option Elab.async false
noncomputable section

structure Fixed (p : NormalizedPacking) extends Points p : Prop where
  southwestMarker : (owners p 5).Inside (33/20) (33/20)
  southeastMarker : (owners p 6).Inside (47/20) (33/20)
  northeastMarker : (owners p 7).Inside (47/20) (47/20)
  northwestMarker : (owners p 8).Inside (33/20) (47/20)
  leftMarker : (owners p 9).Inside (457/500) 2
  bottomMarker : (owners p 10).Inside 2 (457/500)
  rightMarker : (owners p 11).Inside (1543/500) 2
  southeastCorner : (owners p 2).Inside 3 1
  southeastCornerRight : (owners p 2).Inside (1543/500) 1
  northeastCorner : (owners p 3).Inside 3 3
  northwestCorner : (owners p 4).Inside 1 3
  singleton0Seed : (owners p 0).Inside (187/100) (19/25)
  singleton1Seed : (owners p 1).Inside (19/25) (187/100)

theorem fixed (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Fixed p where
  toPoints := points p hf
  southwestMarker := by convert seed p hf 5 (33/20,33/20) (by decide +kernel) using 1 <;> norm_num
  southeastMarker := by convert seed p hf 6 (47/20,33/20) (by decide +kernel) using 1 <;> norm_num
  northeastMarker := by convert seed p hf 7 (47/20,47/20) (by decide +kernel) using 1 <;> norm_num
  northwestMarker := by convert seed p hf 8 (33/20,47/20) (by decide +kernel) using 1 <;> norm_num
  leftMarker := by convert seed p hf 9 (457/500,2) (by decide +kernel) using 1 <;> norm_num
  bottomMarker := by convert seed p hf 10 (2,457/500) (by decide +kernel) using 1 <;> norm_num
  rightMarker := by convert seed p hf 11 (1543/500,2) (by decide +kernel) using 1 <;> norm_num
  southeastCorner := by convert seed p hf 2 (3,1) (by decide +kernel) using 1 <;> norm_num
  southeastCornerRight := by convert seed p hf 2 (1543/500,1) (by decide +kernel) using 1 <;> norm_num
  northeastCorner := by convert seed p hf 3 (3,3) (by decide +kernel) using 1 <;> norm_num
  northwestCorner := by convert seed p hf 4 (1,3) (by decide +kernel) using 1 <;> norm_num
  singleton0Seed := by convert seed p hf 0 (187/100,19/25) (by decide +kernel) using 1 <;> norm_num
  singleton1Seed := by convert seed p hf 1 (19/25,187/100) (by decide +kernel) using 1 <;> norm_num

theorem southwest_south (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 2 (3/2) := by
  have h := fixed p hf
  have point := C981CompletionCrosspoint.point (pullY (pullX (owners p 5))) (side p 5)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestF4)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestG3)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 5 8 (by decide) _ _ h.northwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 5 6 (by decide) _ _ h.southeastMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 5 1 (by decide) _ _
      (singleton_vertical p hf _ (by norm_num) (by norm_num)))
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 5 1 (by decide) _ _
      (singleton_vertical p hf _ (by norm_num) (by norm_num)))
  norm_num [inside_pullY,inside_pullX] at point
  exact point
theorem southwest_west (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside (3/2) 2 := by
  have h := fixed p hf
  have point := C981CompletionCrosspoint.point (pullSwap (pullY (pullX (owners p 5)))) (side p 5)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestG3)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestF4)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 5 6 (by decide) _ _ h.southeastMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 5 8 (by decide) _ _ h.northwestMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 5 0 (by decide) _ _
      (singleton_horizontal p hf _ (by norm_num) (by norm_num)))
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 5 0 (by decide) _ _
      (singleton_horizontal p hf _ (by norm_num) (by norm_num)))
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at point
  exact point

theorem southeast_g8 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 3 (8/5) := by
  have h := fixed p hf
  exact CommonCases.C974976Central.southeast_g8 _ _ (side p 6)
    h.southeastMarker h.southeastF8 h.southeastG h.northeastMarker
    (apart p hf 6 7 (by decide))
    (foreign p hf 6 5 (by decide) _ _ (southwest_south p hf))
    (foreign p hf 6 11 (by decide) _ _ h.rightMarker)
theorem bottom_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 10).Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → (owners p 10).Inside x 1 := by
  have h := fixed p hf
  exact (Completion.OtherCases.C1089.ContinuousBottom.reach (owners p 10) (side p 10) (box p 10)
    h.bottomMarker h.bottomF6 h.bottomG5
    (foreign p hf 10 0 (by decide) _ _ (singleton_horizontal p hf _ (by norm_num) le_rfl))
    (foreign p hf 10 0 (by decide) _ _ h.singleton0Seed)
    (foreign p hf 10 6 (by decide) _ _ h.southeastMarker)).2
theorem right_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside 3 (64/25) := by
  have h := fixed p hf
  have point := WallUpperMissingReach.point (pullX (owners p 11)) (side p 11)
    (container_pullX _ (box p 11))
    (by norm_num [inside_pullX]; exact h.rightMarker)
    (by norm_num [inside_pullX]; exact h.rightG9)
    (by norm_num [inside_pullX]; exact foreign p hf 11 6 (by decide) _ _ h.southeastF8)
    (by norm_num [inside_pullX]; exact foreign p hf 11 7 (by decide) _ _ h.northeastMarker)
  norm_num [inside_pullX] at point
  exact point
theorem right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 113/50≤y) (high : y≤64/25) : (owners p 11).Inside 3 y :=
  CommonCases.OriginalOwners.vertical_segment _ 3 (113/50) (64/25) y
    (fixed p hf).rightF9 (right_reach p hf) (by norm_num) low high

theorem selection_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    CommonCases.C974976Central.Input (owners p 6) (owners p 7) := by
  have h := fixed p hf
  exact {
    sideS := side p 6
    sideE := side p 7
    apart := apart p hf 6 7 (by decide)
    markerS := h.southeastMarker
    f8 := h.southeastF8
    g8 := southeast_g8 p hf
    corner := foreign p hf 6 2 (by decide) _ _ h.southeastCorner
    cornerMarker := foreign p hf 6 2 (by decide) _ _ h.southeastCornerRight
    rightMarker := foreign p hf 6 11 (by decide) _ _ h.rightMarker
    bottom := fun x low high => foreign p hf 6 10 (by decide) _ _ ((bottom_reach p hf).2 x low high)
    markerE := h.northeastMarker
    northwest := foreign p hf 7 8 (by decide) _ _ h.northwestMarker
    f9 := foreign p hf 7 11 (by decide) _ _ h.rightF9
    g9 := foreign p hf 7 11 (by decide) _ _ h.rightG9
    fCover := h.northeastF
    gCover := h.northeastG
    same := same p 6 7
    southwest := foreign p hf 6 5 (by decide) _ _ (southwest_south p hf)
    topMarker := missing_top p hf 7 }
theorem northeast_g7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside (113/50) 3 :=
  CommonCases.C974976Central.northeast_g7 _ _ (selection_input p hf)
theorem northeast_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside (12/5) 3 :=
  CommonCases.C974976Central.northeast_f7 _ _ (selection_input p hf)

theorem northwest_component (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ((owners p 8).Inside (8/5) 3 ∨ (owners p 8).Inside 2 (113/50)) ∧
      (owners p 8).Inside (87/50) 3 := by
  have h := compulsory p hf
  have neF : 7∈actual p 7 := by
    apply (aux p 7 7 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using northeast_f7 p hf
  have neG : 17∈actual p 7 := by
    apply (aux p 7 17 (by norm_num)).mp
    simpa [auxPoints,fPoints,gPoints] using northeast_g7 p hf
  have choices := C972Domains.northwest_cut _ (domain p hf C972Domains.northwest 8 rfl)
    (foreign_aux p hf 8 1 (by decide) 0 h.singleton1.1)
    (foreign_aux p hf 8 9 (by decide) 1 h.left.1)
    (foreign_aux p hf 8 5 (by decide) 4 h.southwest.1)
    (foreign_aux p hf 8 7 (by decide) 7 neF)
    (foreign_aux p hf 8 1 (by decide) 10 h.singleton1.2)
    (foreign_aux p hf 8 9 (by decide) 11 h.left.2)
    (foreign_aux p hf 8 5 (by decide) 13 h.southwest.2)
    (foreign_aux p hf 8 7 (by decide) 17 neG)
  constructor
  · rcases choices.1 with f|f
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 8 3 (by norm_num)).mpr f
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 8 5 (by norm_num)).mpr f
  · simpa [auxPoints,fPoints,gPoints] using (aux p 8 14 (by norm_num)).mpr choices.2

theorem northwest_f3 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside (8/5) 3 := by
  by_contra missing
  have h := fixed p hf
  have choices := northwest_component p hf
  have point := Completion.OtherCases.ElbowPoint.points_original (pullSwap (owners p 8)) (side p 8)
    (by simpa only [inside_pullSwap] using h.northwestMarker)
    (by simpa only [inside_pullSwap] using choices.1.resolve_left missing)
    (by simpa only [inside_pullSwap] using choices.2)
    (by simpa only [inside_pullSwap] using foreign p hf 8 7 (by decide) _ _ h.northeastMarker)
    (by simpa only [inside_pullSwap] using missing)
    (by simpa only [inside_pullSwap] using missing_top p hf 8)
  have samePoint : (owners p 8).Inside (3/2) 2 := by
    simpa only [inside_pullSwap] using point.1
  exact apart p hf 5 8 (by decide) _ _ ⟨southwest_west p hf,samePoint⟩

theorem northwest_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside (8/5) 3 ∧ (owners p 8).Inside (87/50) 3 :=
  ⟨northwest_f3 p hf,(northwest_component p hf).2⟩

end
#print axioms northeast_f7
#print axioms northwest_pair
end N12Compact.FiniteCases.C972

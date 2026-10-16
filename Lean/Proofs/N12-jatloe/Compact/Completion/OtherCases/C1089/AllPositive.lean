import Compact.Completion.OtherCases.C1089.SectorEntrances
import Compact.Completion.C1092.MMMMEnding
import Compact.Completion.C981.Crosspoint
import Compact.Geometry.CentralWallCenter

/-! The all-positive C1089 sector, using the whole continuous MMMM ending
on the actual Q6,Q5,Q7. No C1092 family equality, southwest paired corner
or ownership of the absent marker is asserted. Every foreign point is
provided by its original wall or paired corner. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.AllPositive
open S12 S12Pilot OriginalData WallCore SectorEntrances
set_option Elab.async false
noncomputable section

theorem southeast_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : 2≤centerY (owners p 10)) (top : 2≤centerX (owners p 11)) :
    (owners p 5).Inside 3 (87/50) ∧ (owners p 5).Inside 3 (8/5) := by
  let h := frame p hf
  have ne := northeast_inward p hf right top
  have g8 : (owners p 5).Inside 3 (8/5) := by
    rcases AuxiliaryCover.southeast_g_cover p hf with own | own | own
    · exact False.elim (h.apart 5 9 (by decide) _ _
        ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 5 6 (by decide) _ _ ⟨own,ne.2⟩)
    · exact own
  have fc := AuxiliaryCover.southeast_f_cover p hf
  have result := clockwise_pair (pullSwap (pullY (owners p 5))) (h.side 5)
    (by norm_num [inside_pullSwap,inside_pullY]; exact h.southeastMarker)
    (by norm_num [inside_pullSwap,inside_pullY]; exact g8)
    (by norm_num [inside_pullSwap,inside_pullY]; tauto)
    (by norm_num [inside_pullSwap,inside_pullY]; exact fun own => h.apart 5 6 (by decide) _ _ ⟨own,ne.2⟩)
    (by norm_num [inside_pullSwap,inside_pullY]; exact fun own => h.apart 5 9 (by decide) _ _ ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap,inside_pullY]; exact fun own => h.apart 5 9 (by decide) _ _ ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap,inside_pullY]; exact fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩)
  norm_num [inside_pullSwap,inside_pullY] at result
  exact ⟨result,g8⟩

theorem northwest_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (right : 2≤centerY (owners p 10))
    (top : 2≤centerX (owners p 11)) :
    (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3 := by
  let h := frame p hf
  have ne := northeast_inward p hf right top
  have f3 : (owners p 7).Inside (8/5) 3 := by
    rcases AuxiliaryCover.northwest_f_cover p hf with own | own | own
    · exact False.elim (h.apart 7 8 (by decide) _ _
        ⟨own,left_high p hf left _ (by norm_num) (by norm_num)⟩)
    · exact own
    · exact False.elim (h.apart 7 6 (by decide) _ _ ⟨own,ne.1⟩)
  have gc := AuxiliaryCover.northwest_g_cover p hf
  have result := clockwise_pair (pullX (owners p 7)) (h.side 7)
    (by norm_num [inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullX]; exact f3)
    (by norm_num [inside_pullX]; tauto)
    (by norm_num [inside_pullX]; exact fun own => h.apart 7 6 (by decide) _ _ ⟨own,ne.1⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 7 8 (by decide) _ _ ⟨own,left_high p hf left _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 7 8 (by decide) _ _ ⟨own,left_high p hf left _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullX]; exact fun own => h.apart 7 3 (by decide) _ _ ⟨own,h.northwestCorner⟩)
  norm_num [inside_pullX] at result
  exact ⟨f3,result⟩

/-- The paired northeast corner and one actual foreign halfpoint force
the top origin. Both true walls of that same corner are retained. -/
theorem top_origin (B K : OpenSquare) (side : 1<B.side) (same : B.side=K.side)
    (boxB : InsideContainer B) (boxK : InsideContainer K)
    (markerB : B.Inside 2 (1543/500)) (auxiliaryB : B.Inside (12/5) 3)
    (markerK : K.Inside 3 (1543/500)) (cornerK : K.Inside 3 3)
    (missingK : ¬K.Inside 3 (5/2))
    (apart : ∀ x y,¬(K.Inside x y ∧ B.Inside x y)) : B.Inside 2 3 := by
  have result := WallProfile.boundary_origin (pullY (pullX B)) (pullY (pullX K))
    (457/500) (8/5) side same
    (by
      intro x y own
      have wall := (boxB _ _ ((inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp own))).2.2.2
      linarith only [wall])
    (by
      intro x y own
      have wall := boxK _ _ ((inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp own))
      exact ⟨by linarith only [wall.2.1],by linarith only [wall.2.2.2]⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullY,inside_pullX]; exact markerB)
    (by norm_num [inside_pullY,inside_pullX]; exact auxiliaryB)
    (by norm_num [inside_pullY,inside_pullX]; exact markerK)
    (by norm_num [inside_pullY,inside_pullX]; exact cornerK)
    (by norm_num [inside_pullY,inside_pullX]; exact missingK)
    (fun x y both => apart _ _
      ⟨(inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp both.1),
        (inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp both.2)⟩)
  norm_num [inside_pullY,inside_pullX] at result
  exact result

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (right : 2≤centerY (owners p 10))
    (top : 2≤centerX (owners p 11)) : False := by
  let h := frame p hf
  have ne := northeast_inward p hf right top
  have se := southeast_pair p hf right top
  have nw := northwest_pair p hf left right top
  have rightPair := DirectDomains.right_high_pair p hf
    (fun own => h.apart 10 5 (by decide) _ _ ⟨own,se.1⟩)
  have topF7 := DirectDomains.top_f7 p hf
    (fun own => h.apart 11 7 (by decide) _ _ ⟨own,nw.1⟩)
  have rHalf := CentralWallCenter.right_high _ (h.side 10) (h.box 10) h.rightMarker
    rightPair.2 (fun own => h.apart 10 5 (by decide) _ _ ⟨own,se.1⟩)
    (fun own => h.apart 10 6 (by decide) _ _ ⟨own,ne.2⟩)
  have tHalf : (owners p 11).Inside (5/2) 3 := by
    have point := CentralWallCenter.right_high (pullSwap (owners p 11)) (h.side 11)
      (container_pullSwap _ (h.box 11))
      (by norm_num [inside_pullSwap]; exact h.topMarker)
      (by norm_num [inside_pullSwap]; exact topF7)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 11 7 (by decide) _ _ ⟨own,nw.2⟩)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 11 6 (by decide) _ _ ⟨own,ne.1⟩)
    norm_num [inside_pullSwap] at point
    exact point
  have rOrigin : (owners p 10).Inside 3 2 := by
    have point := top_origin (pullSwap (owners p 10)) (pullSwap (owners p 2))
      (h.side 10) (h.same 10 2) (container_pullSwap _ (h.box 10))
      (container_pullSwap _ (h.box 2))
      (by norm_num [inside_pullSwap]; exact h.rightMarker)
      (by norm_num [inside_pullSwap]; exact rightPair.2)
      (by norm_num [inside_pullSwap]; exact h.northeastCornerRight)
      (by norm_num [inside_pullSwap]; exact h.northeastCorner)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 2 11 (by decide) _ _ ⟨own,tHalf⟩)
      (fun x y both => h.apart 2 10 (by decide) _ _
        ⟨(inside_pullSwap _ _ _).mp both.1,(inside_pullSwap _ _ _).mp both.2⟩)
    exact (inside_pullSwap _ _ _).mp point
  have tOrigin := top_origin _ _ (h.side 11) (h.same 11 2) (h.box 11) (h.box 2)
    h.topMarker topF7 h.northeastCornerTop h.northeastCorner
    (fun own => h.apart 2 10 (by decide) _ _ ⟨own,rHalf⟩) (h.apart 2 11 (by decide))
  have center := CentralWallCenter.point (owners p 6) (owners p 10) (owners p 11)
    (h.side 6) (h.same 6 10) (h.same 6 11) (h.box 10) (h.box 11) ne.1 ne.2 h.northeastMarker
    (fun own => h.apart 6 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
    (fun own => h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    h.rightMarker rightPair.2 (fun own => h.apart 10 5 (by decide) _ _ ⟨own,se.1⟩)
    h.topMarker topF7 (fun own => h.apart 11 7 (by decide) _ _ ⟨own,nw.2⟩)
    (h.apart 6 10 (by decide)) (h.apart 6 11 (by decide))
  have halfY := C981CompletionCrosspoint.point (owners p 6) (h.side 6)
    ne.1 ne.2 h.northeastMarker
    (fun own => h.apart 6 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
    (fun own => h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (fun own => h.apart 6 10 (by decide) _ _ ⟨own,rightPair.2⟩)
    (fun own => h.apart 6 10 (by decide) _ _ ⟨own,rHalf⟩)
  have halfX : (owners p 6).Inside (5/2) 2 := by
    have point := C981CompletionCrosspoint.point (pullSwap (owners p 6)) (h.side 6)
      (by norm_num [inside_pullSwap]; exact ne.2)
      (by norm_num [inside_pullSwap]; exact ne.1)
      (by norm_num [inside_pullSwap]; exact h.northeastMarker)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 11 (by decide) _ _ ⟨own,topF7⟩)
      (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 11 (by decide) _ _ ⟨own,tHalf⟩)
    norm_num [inside_pullSwap] at point
    exact point
  have innerX : (owners p 6).Inside (239/100) 2 :=
    CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ center halfX
      (by norm_num) (by norm_num) (by norm_num)
  have innerY : (owners p 6).Inside 2 (239/100) :=
    CommonCases.OriginalOwners.vertical_segment _ _ _ _ _ center halfY
      (by norm_num) (by norm_num) (by norm_num)
  let N := (owners p 6).translated 2 2
  let E := (owners p 5).translated 2 2
  let W := (owners p 7).translated 2 2
  have data : C1092MMMMEnding.Data N E W := {
    side := h.side 6
    sameE := h.same 6 5
    sameW := h.same 6 7
    origin := by norm_num [N,inside_translated_iff]; exact center
    halfX := by norm_num [N,inside_translated_iff]; exact halfX
    halfY := by norm_num [N,inside_translated_iff]; exact halfY
    markerN := by norm_num [N,inside_translated_iff]; exact h.northeastMarker
    markerE := by norm_num [E,inside_translated_iff]; exact h.southeastMarker
    ordinaryE1 := by norm_num [E,inside_translated_iff]; exact se.1
    ordinaryE2 := by norm_num [E,inside_translated_iff]; exact se.2
    markerW := by norm_num [W,inside_translated_iff]; exact h.northwestMarker
    ordinaryW1 := by norm_num [W,inside_translated_iff]; exact nw.2
    ordinaryW2 := by norm_num [W,inside_translated_iff]; exact nw.1
    eLeftBottom := by norm_num [E,inside_translated_iff]; exact fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩
    eLeftTop := by norm_num [E,inside_translated_iff]; exact fun own => h.apart 5 10 (by decide) _ _ ⟨own,rOrigin⟩
    eRightBottom := by norm_num [E,inside_translated_iff]; exact fun own => h.apart 5 9 (by decide) _ _ ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩
    eRightTop := by norm_num [E,inside_translated_iff]; exact fun own => h.apart 5 6 (by decide) _ _ ⟨own,innerX⟩
    wLeftBottom := by norm_num [W,inside_translated_iff]; exact fun own => h.apart 7 3 (by decide) _ _ ⟨own,h.northwestCorner⟩
    wLeftTop := by norm_num [W,inside_translated_iff]; exact fun own => h.apart 7 11 (by decide) _ _ ⟨own,tOrigin⟩
    wRightBottom := by norm_num [W,inside_translated_iff]; exact fun own => h.apart 7 8 (by decide) _ _ ⟨own,left_high p hf left _ (by norm_num) (by norm_num)⟩
    wRightTop := by norm_num [W,inside_translated_iff]; exact fun own => h.apart 7 6 (by decide) _ _ ⟨own,innerY⟩
    apartE := fun x y both => h.apart 6 5 (by decide) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
    apartW := fun x y both => h.apart 6 7 (by decide) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩ }
  exact C1092MMMMEnding.impossible N E W data

end
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.AllPositive

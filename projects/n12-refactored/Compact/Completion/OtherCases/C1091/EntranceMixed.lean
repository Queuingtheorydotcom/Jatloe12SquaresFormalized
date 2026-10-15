import Compact.Completion.OtherCases.C1091.EntranceAllPositive
import Compact.Completion.CommonCases.InwardPoint

/-! The C1091 closed (++,-) sector. The genuine merged square owns
one of two points. The northwest square owns both, using a real top-wall
advance and the correctly reflected strong inward point (1.46,2.01).
No singleton inner corner or globally absent marker is assumed. Source only. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceMixed
open S12 S12Pilot OriginalData EntranceFrame EntranceWalls
set_option Elab.async false
noncomputable section

abbrev clockwise_pair := C1089.SectorEntrances.clockwise_pair

theorem northeast_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (right : 2≤centerY (owners p 10))
    (top : centerX (owners p 11)≤2) :
    (owners p 6).Inside (12/5) 3 ∧ (owners p 6).Inside (113/50) 3 := by
  let h := frame p hf
  have nw := northwest_inward p hf left top
  have f7 : (owners p 6).Inside (12/5) 3 := by
    rcases EntranceDomains.northeast_f p hf with own | own | own
    · exact False.elim (h.apart 6 7 (by decide) _ _ ⟨own,nw.1⟩)
    · exact own
    · exact False.elim (h.apart 6 10 (by decide) _ _
        ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
  exact ⟨f7,clockwise_pair _ (h.side 6) h.northeastMarker f7
    (EntranceDomains.northeast_g p hf)
    (fun own => h.apart 6 7 (by decide) _ _ ⟨own,nw.1⟩)
    (fun own => h.apart 6 10 (by decide) _ _
      ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 6 10 (by decide) _ _
      ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)⟩


theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : 2≤centerY (owners p 10)) (top : centerX (owners p 11)≤2) : False := by
  let h := frame p hf
  have left := (left_above p hf).le
  have nw := northwest_inward p hf left top
  have ne := northeast_pair p hf left right top
  have topF3 : (owners p 11).Inside (8/5) 3 := by
    rcases EntranceDomains.top_component p hf with own|pair
    · exact False.elim (h.apart 11 6 (by decide) _ _ ⟨own,ne.2⟩)
    · exact pair.1
  have missingF3 : ¬(owners p 7).Inside (8/5) 3 :=
    fun own => h.apart 7 11 (by decide) _ _ ⟨own,topF3⟩
  have topLow := C1089.WallOrigins.top_left_advance (owners p) (h.side 11)
    (h.box 11) h.apart h.topMarker topF3 ne.2 h.northwestMarker
  have topMiddle : (owners p 11).Inside (3/2) 3 := by
    convert inside_segment (owners p 11) (36/25) 3 (8/5) 3 (3/8)
      topLow topF3 (by norm_num) (by norm_num) using 1 <;> norm_num
  have halfpoint : (owners p 7).Inside (3/2) 2 := by
    have result := C981CompletionCrosspoint.point (pullSwap (pullX (owners p 7))) (h.side 7)
      (by norm_num [inside_pullSwap,inside_pullX]; exact nw.2)
      (by norm_num [inside_pullSwap,inside_pullX]; exact nw.1)
      (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestMarker)
      (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
        h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
        h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
      (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
        h.apart 7 11 (by decide) _ _ ⟨own,topF3⟩)
      (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
        h.apart 7 11 (by decide) _ _ ⟨own,topMiddle⟩)
    norm_num [inside_pullSwap,inside_pullX] at result
    exact result
  have strong : (owners p 7).Inside (73/50) (201/100) := by
    have result := CommonCases.InwardPoint.strong_original
      (pullY (pullX (owners p 7))) (h.side 7)
      (by norm_num [inside_pullY,inside_pullX]; exact h.northwestMarker)
      (by norm_num [inside_pullY,inside_pullX]; exact nw.1)
      (by norm_num [inside_pullY,inside_pullX]; exact nw.2)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact missingF3)
    norm_num [inside_pullY,inside_pullX] at result
    exact result
  rcases EntranceMergedLow.alternative_original p hf with own|own
  · exact h.apart 4 7 (by decide) _ _ ⟨own,halfpoint⟩
  · exact h.apart 4 7 (by decide) _ _ ⟨own,strong⟩

end
#print axioms northeast_pair
end N12Compact.Completion.OtherCases.C1091.EntranceMixed

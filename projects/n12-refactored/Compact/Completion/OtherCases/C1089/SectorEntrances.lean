import Compact.Completion.OtherCases.C1089.WallCore
import Compact.Completion.OtherCases.C1089.MMMPSingletonEnding
import Compact.Completion.OtherCases.C1089.LastSectorRawEnding

/-! The remaining ordinary pairs in C1089's three incoming sectors.
Every cover is a proved actual-family cover. The single reusable corner
argument retains exact .26/.39 gaps, actual corner ownership and weak
exits, and is transported with all of its point data simultaneously.
Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.SectorEntrances
open S12 S12Pilot OriginalData WallCore
set_option Elab.async false
noncomputable section

/-- An outer top anchor forces its adjoining top auxiliary. -/
theorem clockwise_pair (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20)) (top : q.Inside (12/5) 3)
    (gcover : q.Inside (113/50) 2 ∨ q.Inside (113/50) 3 ∨ q.Inside 3 (12/5))
    (inward : ¬q.Inside 2 (113/50)) (right : ¬q.Inside 3 (113/50))
    (gap : ¬q.Inside 3 (239/100)) (corner : ¬q.Inside 3 3) :
    q.Inside (113/50) 3 := by
  by_contra absent
  have noOuter : ¬q.Inside 3 (12/5) := by
    intro outer
    exact C1092CornerTwoGaps.impossible q side (13/50) (39/100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      marker top outer (by norm_num; exact absent) (by norm_num; exact gap) corner
  rcases gcover with own | own | own
  · exact C1092MixedSpan.impossible (pullSwap (pullX q)) side
      (by norm_num [inside_pullSwap,inside_pullX]; exact own)
      (by norm_num [inside_pullSwap,inside_pullX]; exact top)
      (by norm_num [inside_pullSwap,inside_pullX]; exact inward)
      (by norm_num [inside_pullSwap,inside_pullX]; exact absent)
      (by norm_num [inside_pullSwap,inside_pullX]; exact right)
      (by norm_num [inside_pullSwap,inside_pullX]; exact noOuter)
  · exact absent own
  · exact noOuter own

theorem mmmp_ne_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (right : 2≤centerY (owners p 10))
    (top : centerX (owners p 11)≤2) :
    (owners p 6).Inside (12/5) 3 ∧ (owners p 6).Inside (113/50) 3 := by
  let h := frame p hf
  have nw := northwest_inward p hf left top
  have f7 : (owners p 6).Inside (12/5) 3 := by
    rcases AuxiliaryCover.northeast_f_cover p hf with own | own | own
    · exact False.elim (h.apart 6 7 (by decide) _ _ ⟨own,nw.1⟩)
    · exact own
    · exact False.elim (h.apart 6 10 (by decide) _ _
        ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
  exact ⟨f7,clockwise_pair _ (h.side 6) h.northeastMarker f7
    (AuxiliaryCover.northeast_g_cover p hf)
    (fun own => h.apart 6 7 (by decide) _ _ ⟨own,nw.1⟩)
    (fun own => h.apart 6 10 (by decide) _ _
      ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 6 10 (by decide) _ _
      ⟨own,right_high p hf right _ (by norm_num) (by norm_num)⟩)
    (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)⟩

theorem mmmp_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (right : 2≤centerY (owners p 10))
    (top : centerX (owners p 11)≤2) : False := by
  let h := frame p hf
  have nw := northwest_inward p hf left top
  have ne := mmmp_ne_pair p hf left right top
  have topF3 : (owners p 11).Inside (8/5) 3 := by
    rcases DirectDomains.top_component p hf with own | pair
    · exact False.elim (h.apart 11 6 (by decide) _ _ ⟨own,ne.2⟩)
    · exact pair.1
  exact MMMPSingletonEnding.impossible (owners p) {
    side := h.side
    topContained := h.box 11
    apart := h.apart
    singletonNear := h.singletonNear
    singletonFar := h.singletonFar
    absentMarker := h.absentMarker 4
    southwestMarker := h.southwestMarker
    southwestF := AuxiliaryCover.southwest_f_cover p hf
    southwestG := AuxiliaryCover.southwest_g_cover p hf
    northeastMarker := h.northeastMarker
    northeastG7 := ne.2
    northwestMarker := h.northwestMarker
    northwestF5 := nw.1
    northwestG3 := nw.2
    leftMarker := h.leftMarker
    topMarker := h.topMarker
    topF3 := topF3 }

/-- The transposed MMMP pair, in the literal original northeast owner. -/
theorem last_ne_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5) := by
  let h := frame p hf
  have se := southeast_inward p hf right
  have g9 : (owners p 6).Inside 3 (12/5) := by
    rcases AuxiliaryCover.northeast_g_cover p hf with own | own | own
    · exact False.elim (h.apart 6 5 (by decide) _ _ ⟨own,se.2⟩)
    · exact False.elim (h.apart 6 11 (by decide) _ _
        ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    · exact own
  have fc := AuxiliaryCover.northeast_f_cover p hf
  have result := clockwise_pair (pullSwap (owners p 6)) (h.side 6)
    (by norm_num [inside_pullSwap]; exact h.northeastMarker)
    (by norm_num [inside_pullSwap]; exact g9)
    (by norm_num [inside_pullSwap]; tauto)
    (by norm_num [inside_pullSwap]; exact fun own =>
      h.apart 6 5 (by decide) _ _ ⟨own,se.2⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 11 (by decide) _ _
      ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 11 (by decide) _ _
      ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own =>
      h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
  norm_num [inside_pullSwap] at result
  exact ⟨result,g9⟩

theorem last_left_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5) := by
  let h := frame p hf
  have se := southeast_inward p hf right
  have f0 : (owners p 4).Inside 1 (87/50) := by
    rcases AuxiliaryCover.southwest_f_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _
        ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 4 5 (by decide) _ _ ⟨own,se.1⟩)
  exact DirectDomains.left_pair p hf
    (fun own => h.apart 8 4 (by decide) _ _ ⟨own,f0⟩)

theorem last_right_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5) := by
  let h := frame p hf
  exact DirectDomains.right_low_pair p hf
    (fun own => h.apart 10 6 (by decide) _ _ ⟨own,(last_ne_pair p hf right top).1⟩)

end
#print axioms mmmp_impossible
#print axioms last_ne_pair
end N12Compact.Completion.OtherCases.C1089.SectorEntrances

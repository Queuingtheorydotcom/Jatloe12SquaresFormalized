import Compact.Completion.OtherCases.C1089.SectorEntrances
import Compact.Completion.OtherCases.C1089.ContinuousActual

/-! Two complete C1089 sector endings from their literal original owners:
the opposed inward centers and the northeast-inward strict duplicate.
No singleton inner corner, square angle or center support is an input.
The closed center cuts and weak exclusions include tangencies. Source only.
-/
namespace N12Compact.Completion.OtherCases.C1089.SectorEndings
open S12 S12Pilot OriginalData WallCore SectorEntrances
set_option Elab.async false
noncomputable section

theorem opposed_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : 2≤centerY (owners p 8)) (right : centerY (owners p 10)≤2)
    (top : centerX (owners p 11)≤2) : False := by
  let h := frame p hf
  have se := southeast_inward p hf right
  have nw := northwest_inward p hf left top
  have aF0 : (owners p 4).Inside 1 (87/50) := by
    rcases AuxiliaryCover.southwest_f_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _
        ⟨own,singleton_bar p hf _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 4 5 (by decide) _ _ ⟨own,se.1⟩)
  have aG0 : (owners p 4).Inside 1 (8/5) := by
    rcases AuxiliaryCover.southwest_g_cover p hf with own | own | own
    · exact own
    · exact False.elim (h.apart 4 0 (by decide) _ _ ⟨own,h.singletonFar⟩)
    · exact False.elim (h.apart 4 7 (by decide) _ _ ⟨own,nw.2⟩)
  have leftG1 : (owners p 8).Inside 1 (12/5) := by
    rcases AuxiliaryCover.left_g_cover p hf with own | own | own
    · exact False.elim (h.apart 8 4 (by decide) _ _ ⟨own,aG0⟩)
    · exact own
    · exact False.elim (h.apart 8 7 (by decide) _ _ ⟨own,nw.2⟩)
  have sc := ContinuousActual.southeast (owners p) h.side h.same h.box h.apart
    h.southeastMarker se.1 se.2 h.southwestMarker h.rightMarker
    (right_low p hf right _ (by norm_num) (by norm_num)) right
    h.bottomMarker (DirectDomains.bottom_far p hf) h.singletonFar
    h.southeastCornerRight h.southeastCorner
  have nc := ContinuousActual.northwest (owners p) h.side h.same h.box h.apart
    h.northwestMarker nw.2 nw.1 h.southwestMarker h.topMarker
    (top_low p hf top _ (by norm_num) (by norm_num)) top
    h.leftMarker leftG1 aF0 h.northwestCornerTop h.northwestCorner
  exact h.apart 5 7 (by decide) _ _ ⟨sc.1,nc.1⟩

/-- Both outward duplicate points have the same original S and one
whole actual bottom bar. The paired southeast corner supplies both of
its separate strict anchors. -/
theorem southeast_duplicates (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f8 : (owners p 5).Inside 3 (87/50))
    (g8 : (owners p 5).Inside 3 (8/5))
    (missing : ¬(owners p 5).Inside (113/50) 2) :
    (owners p 5).Inside (123/50) (201/100) ∧
      (owners p 5).Inside (5/2) (51/25) := by
  let h := frame p hf
  let S := pullY (owners p 5)
  have m : S.Inside (47/20) (47/20) := by
    norm_num [S,inside_pullY]; exact h.southeastMarker
  have a : S.Inside 3 (113/50) := by norm_num [S,inside_pullY]; exact f8
  have b : S.Inside 3 (12/5) := by norm_num [S,inside_pullY]; exact g8
  have d : ¬S.Inside (113/50) 2 := by norm_num [S,inside_pullY]; exact missing
  have r : ¬S.Inside (1543/500) 2 := by
    norm_num [S,inside_pullY]
    exact fun own => h.apart 5 10 (by decide) _ _ ⟨own,h.rightMarker⟩
  have k : ¬S.Inside 3 3 := by
    norm_num [S,inside_pullY]
    exact fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩
  have cornerMark : ¬S.Inside (1543/500) 3 := by
    norm_num [S,inside_pullY]
    exact fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCornerRight⟩
  have bar (x : ℝ) (low : 113/50≤x) (high : x≤14/5) : ¬S.Inside x 3 := by
    norm_num [S,inside_pullY]
    exact fun own => h.apart 5 9 (by decide) _ _ ⟨own,(bottom p hf).2.2 x low high⟩
  have first := CommonCases.OutwardPoint.point_original S (h.side 5) m a b d r k cornerMark bar
  have second := ShortDuplicatePoints.outward_of_bar S (h.side 5) m a b d r k cornerMark bar
  norm_num [S,inside_pullY] at first second
  exact ⟨first,second⟩

theorem northeast_inward_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (left : centerY (owners p 8)≤2) (right : 2≤centerY (owners p 10))
    (top : 2≤centerX (owners p 11)) : False := by
  let h := frame p hf
  have a := southwest_inward p hf left
  have e := northeast_inward p hf right top
  have f8 : (owners p 5).Inside 3 (87/50) := by
    rcases AuxiliaryCover.southeast_f_cover p hf with own | own | own
    · exact False.elim (h.apart 5 4 (by decide) _ _ ⟨own,a.1⟩)
    · exact False.elim (h.apart 5 9 (by decide) _ _ ⟨own,DirectDomains.bottom_far p hf⟩)
    · exact own
  have g8 : (owners p 5).Inside 3 (8/5) := by
    rcases AuxiliaryCover.southeast_g_cover p hf with own | own | own
    · exact False.elim (h.apart 5 9 (by decide) _ _
        ⟨own,(bottom p hf).2.2 _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (h.apart 5 6 (by decide) _ _ ⟨own,e.2⟩)
    · exact own
  have points := southeast_duplicates p hf f8 g8
    (fun own => h.apart 5 6 (by decide) _ _ ⟨own,e.2⟩)
  by_cases f7 : (owners p 6).Inside (12/5) 3
  · have point := ShortDuplicatePoints.inward_original (owners p 6) (h.side 6)
      h.northeastMarker e.1 e.2 f7
      (fun own => h.apart 6 11 (by decide) _ _
        ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
      (fun own => h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (fun own => h.apart 6 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
    exact h.apart 5 6 (by decide) _ _ ⟨points.2,point⟩
  · have point := CommonCases.InwardPoint.point_original (pullY (owners p 6)) (h.side 6)
      (by norm_num [inside_pullY]; exact h.northeastMarker)
      (by norm_num [inside_pullY]; exact e.1)
      (by norm_num [inside_pullY]; exact e.2)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
      (by norm_num [inside_pullY]; exact fun own =>
        h.apart 6 5 (by decide) _ _ ⟨own,h.southeastMarker⟩)
      (by norm_num [inside_pullY]; exact f7)
    norm_num [inside_pullY] at point
    exact h.apart 5 6 (by decide) _ _ ⟨points.1,point⟩

end
#print axioms opposed_impossible
#print axioms northeast_inward_impossible
end N12Compact.Completion.OtherCases.C1089.SectorEndings

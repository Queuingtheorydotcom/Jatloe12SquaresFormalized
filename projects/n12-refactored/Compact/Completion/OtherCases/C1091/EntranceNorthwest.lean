import Compact.Completion.OtherCases.C1091.EntranceMergedShallow
import Compact.Completion.OtherCases.C1091.EntranceNorthwestPoints
import Compact.Completion.OtherCases.C1091.EntranceResidual
import Compact.Completion.OtherCases.ElbowPoint
import Compact.Completion.CommonCases.InwardPoint

/-! Reconstruction of the missing northwest F3 entrance. The genuine
merged markers replace the old C1089 absent-marker1 argument. Q0 and Q8
supply their respective omissions. In the G3 branch the actual southeast
center is foreign to Q7, and the two valid duplicate targets are (1.6,2)
and (1.46,2.01). The G4 branch duplicates (1.5,2). Source only.
-/
namespace N12Compact.Completion.OtherCases.C1091.EntranceNorthwest
open S12 S12Pilot OriginalData EntranceFrame EntranceWalls
set_option Elab.async false
noncomputable section

theorem merged_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 4).Inside (73/50) (199/100) ∧
      (owners p 4).Inside (3/2) 2 ∧ (owners p 4).Inside (79/50) 2 := by
  let h := frame p hf
  have corner := EntranceResidual.singleton_corner p hf right top
  exact EntranceMergedShallow.original_points _ (h.side 4) h.mergedLeft h.southwestMarker
    (fun own => h.apart 4 0 (by decide) _ _ ⟨own,corner⟩)
    (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)

/-- The left owner excludes F1/G1. Missing F3 therefore leaves F5 and
one of G3,G4. No actual owner is assigned merely from an omitted point. -/
theorem northwest_f3 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 7).Inside (8/5) 3 := by
  let h := frame p hf
  have left := EntranceDomains.left_pair p hf
  have merged := merged_points p hf right top
  by_contra missingF3
  have f5 : (owners p 7).Inside 2 (113/50) := by
    rcases EntranceDomains.northwest_f p hf with own|own|own
    · exact False.elim (h.apart 7 8 (by decide) _ _ ⟨own,left.1⟩)
    · exact False.elim (missingF3 own)
    · exact own
  by_cases g3 : (owners p 7).Inside (87/50) 2
  · have inward := CommonCases.InwardPoint.strong_original
      (pullY (pullX (owners p 7))) (h.side 7)
      (by norm_num [inside_pullY,inside_pullX]; exact h.northwestMarker)
      (by norm_num [inside_pullY,inside_pullX]; exact f5)
      (by norm_num [inside_pullY,inside_pullX]; exact g3)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact fun own =>
        h.apart 7 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
      (by norm_num [inside_pullY,inside_pullX]; exact missingF3)
    norm_num [inside_pullY,inside_pullX] at inward
    have corner := EntranceResidual.singleton_corner p hf right top
    have alternatives := EntranceNorthwestPoints.merged_alternative_original _ (h.side 4)
      h.mergedLeft h.southwestMarker
      (fun own => h.apart 4 0 (by decide) _ _ ⟨own,corner⟩)
      (fun own => h.apart 4 8 (by decide) _ _ ⟨own,h.leftMarker⟩)
    rcases alternatives with low | strong
    · have point := EntranceNorthwestPoints.northwest_low _ (h.side 7)
        h.northwestMarker g3 f5 inward missingF3
        (fun own => h.apart 7 5 (by decide) _ _
          ⟨own,(southeast_center p hf right).1⟩)
      exact h.apart 4 7 (by decide) _ _ ⟨low,point⟩
    · exact h.apart 4 7 (by decide) _ _ ⟨strong,inward⟩
  · have g4 : (owners p 7).Inside (87/50) 3 := by
      rcases EntranceDomains.northwest_g p hf with own|own|own
      · exact False.elim (h.apart 7 8 (by decide) _ _ ⟨own,left.2⟩)
      · exact False.elim (g3 own)
      · exact own
    have points := ElbowPoint.points_original (pullSwap (owners p 7)) (h.side 7)
      (by norm_num [inside_pullSwap]; exact h.northwestMarker)
      (by norm_num [inside_pullSwap]; exact f5)
      (by norm_num [inside_pullSwap]; exact g4)
      (by norm_num [inside_pullSwap]; exact fun own =>
        h.apart 7 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
      (by norm_num [inside_pullSwap]; exact missingF3)
      (by norm_num [inside_pullSwap]; exact fun own =>
        h.apart 7 11 (by decide) _ _ ⟨own,h.topMarker⟩)
    norm_num [inside_pullSwap] at points
    exact h.apart 4 7 (by decide) _ _ ⟨merged.2.1,points.1⟩

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) : False :=
  EntranceResidual.impossible_of_northwest p hf right top (northwest_f3 p hf right top)

end
#print axioms northwest_f3
#print axioms impossible
end N12Compact.Completion.OtherCases.C1091.EntranceNorthwest

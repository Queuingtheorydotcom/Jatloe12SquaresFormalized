import Compact.Completion.OtherCases.C983.SharpApplications
import Compact.Completion.OtherCases.OutwardBarFrame

/-! The actual reflected southeast frame, before any coupled support
comparison. Every required foreign marker, corner and bottom bar is retained. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem southeast_outward_frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f8 : 8∈actual p 5) (g8 : 18∈actual p 5) (noG6 : 16∉actual p 5) :
    ∃ r : OpenSquare,0<r.c ∧ 0≤r.s ∧ r.s≤r.c ∧ r.side=(owners p 5).side ∧
      (∀ x y,r.Inside x y ↔ (pullY (owners p 5)).Inside x y) ∧
      OutwardBarPoint.Faces (r.translated 2 2) := by
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have outward : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) f8
    simpa [auxPoints,fPoints,gPoints] using h
  have upper : (owners p 5).Inside 3 (8/5) := by
    have h := auxiliary_inside p 5 18 (by decide +kernel) g8
    simpa [auxPoints,fPoints,gPoints] using h
  have missingG : ¬(owners p 5).Inside (113/50) 2 := by
    have h := missing_auxiliary p 5 16 (by decide +kernel) noG6
    simpa [auxPoints,fPoints,gPoints] using h
  have right : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have corner : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owners p 2).Inside (1543/500) 1 := by
    have h := seed_inside p hf 2 (1543/500,1) (by decide +kernel)
    norm_num at h
    exact h
  have missingR : ¬(owners p 5).Inside (1543/500) 2 :=
    fun h => owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨h,right⟩
  have missingP : ¬(owners p 5).Inside 3 1 :=
    fun h => owners_apart p hf 5 2 (by decide +kernel) _ _ ⟨h,corner⟩
  have missingH : ¬(owners p 5).Inside (1543/500) 1 :=
    fun h => owners_apart p hf 5 2 (by decide +kernel) _ _ ⟨h,cornerMarker⟩
  have point := OutwardBarFrame.frame_original (pullY (owners p 5)) (owners_side p 5)
    (by norm_num only [inside_pullY]; exact marker)
    (by norm_num only [inside_pullY]; exact outward)
    (by norm_num only [inside_pullY]; exact upper)
    (by norm_num only [inside_pullY]; exact missingG)
    (by norm_num only [inside_pullY]; exact missingR)
    (by norm_num only [inside_pullY]; exact missingP)
    (by norm_num only [inside_pullY]; exact missingH)
    (by
      intro z lower upper h
      have own : (owners p 5).Inside z 1 := by
        norm_num only [inside_pullY] at h
        exact h
      exact owners_apart p hf 5 9 (by decide +kernel) z 1
        ⟨own,bottom_bar p hf z lower upper⟩)
  exact point

end
#print axioms southeast_outward_frame
end N12Compact.Completion.OtherCases.C983


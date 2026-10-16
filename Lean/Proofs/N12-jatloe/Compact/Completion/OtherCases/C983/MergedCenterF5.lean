import Compact.Completion.OtherCases.C983.MergedTopExclusion
import Compact.Completion.OtherCases.C983.F5Filters
import Compact.Geometry.MergedLeftNegative

/-! The original merged F5 owner has a strict center. Its positive sector
is an elementary band completion; the negative sector reuses the complete
actual left-wall theorem with the separately proved original F3 absence. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f5_merged_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : (owners p 7).Inside 2 2 := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 7).Inside 2 (113/50) := by
    have h := auxiliary_inside p 7 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  have leftLow : (owners p 1).Inside 1 (87/50) := by
    have h := seed_inside p hf 1 (1,87/50) (by decide +kernel)
    norm_num at h
    exact h
  have lowMissing : ¬(owners p 7).Inside 1 (87/50) :=
    fun h => owners_apart p hf 7 1 (by decide +kernel) _ _ ⟨h,leftLow⟩
  have highMissing : ¬(owners p 7).Inside 1 (113/50) :=
    fun h => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨h,(left_aux p hf).1⟩
  have topMissing : ¬(owners p 7).Inside (8/5) 3 := by
    have h := missing_auxiliary p 7 3 (by decide +kernel) (merged_no_f3 p hf)
    simpa [auxPoints,fPoints,gPoints] using h
  have leftMarker : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame (owners p 7)
  have bottom := (same _ _).mpr south
  have top := (same _ _).mpr north
  have f := (same _ _).mpr inner
  have bounds := abs_le.mp range
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · refine ⟨?_,?_,?_,?_⟩
    · linarith only [bottom.1,cp,sign]
    · linarith only [f.2.1,sign]
    · linarith only [bottom.2.2.1,bounds.2]
    · linarith only [top.2.2.2,cp,sign]
  · exact MergedLeftNegative.point r (owners p 8)
      (by simpa only [shape] using owners_side p 7)
      (shape.trans (owners_same_side p 7 8)) (owners_contained p 8) cp
      (le_of_not_ge sign) (by linarith only [bounds.1]) bottom top
      (fun h => lowMissing ((same _ _).mp h))
      (fun h => highMissing ((same _ _).mp h))
      (fun h => topMissing ((same _ _).mp h)) leftMarker (left_aux p hf).2
      (fun x y h => owners_apart p hf 7 8 (by decide +kernel) x y
        ⟨(same _ _).mp h.1,h.2⟩)

end
#print axioms f5_merged_center
end N12Compact.Completion.OtherCases.C983


import Compact.Completion.OtherCases.C1090.DirectDomains
import Compact.Completion.OtherCases.C1090.RowIdentity
import Compact.Completion.CommonCases.WallSignFromSingleton

/-! Complete actual-family producer for C1090's thirteen entrance facts.
The merged left owner is one actual4098 square; the southwest1 owner
remains a singleton. The five coarse covers are the genuine direct
certificate consequences. The two extra combined domains use the actual
family budget, without a stored joint catalogue or a foreign family theorem.
The continuous ending and original row574 adapter are then unconditional
source contracts. All new source remains uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.OriginalData
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem member (i : Fin 12) : masks i∈family := by
  have checked : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact checked i

private theorem injective : Function.Injective masks := by decide +kernel

private theorem owner_apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) :=
  CommonCases.OriginalOwners.apart family p hf (masks i) (masks j)
    (member i) (member j) (fun equal => different (injective equal))

/-- Every field of the former finite entrance is now supplied from the
actual packing. No wall-center sign, crosspoint or auxiliary signature
has been added as an assumption. -/
theorem auxiliary_entrance (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    AuxiliaryEntrance (owners p) := by
  have near : (owners p 0).Inside (28/25) 1 := by
    have h := seed p hf 0 (28/25,1) (by decide +kernel)
    norm_num at h
    exact h
  have far : (owners p 0).Inside (87/50) 1 := by
    have h := seed p hf 0 (87/50,1) (by decide +kernel)
    norm_num at h
    exact h
  have singletonF2 : (owners p 0).Inside (8/5) 1 :=
    CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ near far
      (by norm_num) (by norm_num) (by norm_num)
  have leftMarker : (owners p 8).Inside (457/500) 2 := by
    have h := seed p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have leftBar := MergedLeftSeed.actual_segment (owners p)
    (CommonCases.OriginalOwners.side p (masks 8))
    (CommonCases.OriginalOwners.box p (masks 8))
    (marker1_owned p hf) leftMarker
  have southwestF4 : (owners p 4).Inside 2 (87/50) := by
    rcases AuxiliaryCover.southwest_f_cover p hf with low | lower | own
    · exact False.elim (owner_apart p hf 4 8 (by decide) _ _
        ⟨low,leftBar _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (owner_apart p hf 4 0 (by decide) _ _ ⟨lower,singletonF2⟩)
    · exact own
  have southwestG3 : (owners p 4).Inside (87/50) 2 := by
    rcases AuxiliaryCover.southwest_g_cover p hf with low | lower | own
    · exact False.elim (owner_apart p hf 4 8 (by decide) _ _
        ⟨low,leftBar _ (by norm_num) (by norm_num)⟩)
    · exact False.elim (owner_apart p hf 4 0 (by decide) _ _ ⟨lower,far⟩)
    · exact own
  have bottomF6 : (owners p 9).Inside (12/5) 1 := by
    rcases AuxiliaryCover.bottom_f_cover p hf with low | middle | own
    · exact False.elim (owner_apart p hf 9 0 (by decide) _ _ ⟨low,singletonF2⟩)
    · exact False.elim (owner_apart p hf 9 4 (by decide) _ _ ⟨middle,southwestF4⟩)
    · exact own
  have southeastF8 : (owners p 5).Inside 3 (87/50) := by
    rcases AuxiliaryCover.southeast_f_cover p hf with middle | lower | own
    · exact False.elim (owner_apart p hf 5 4 (by decide) _ _ ⟨middle,southwestF4⟩)
    · exact False.elim (owner_apart p hf 5 9 (by decide) _ _ ⟨lower,bottomF6⟩)
    · exact own
  have bottomChord := CommonCases.WallSignFromSingleton.original_bottom family p hf 8192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have bottomG5 : (owners p 9).Inside (113/50) 1 := by
    exact bottomChord.2 _ (by norm_num) (by norm_num)
  have rightMissing : 8∉CommonCases.OriginalOwners.auxiliaries p 16384 := by
    intro own
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 16384 8 (by norm_num)).mpr own
    have actual : (owners p 10).Inside 3 (87/50) := by
      simpa [owners,masks,auxPoints,fPoints,gPoints] using point
    exact owner_apart p hf 10 5 (by decide) _ _ ⟨actual,southeastF8⟩
  have rightPair := DirectDomains.right_points p hf rightMissing
  exact {
    southwestF4 := southwestF4
    southwestG3 := southwestG3
    southeastF8 := southeastF8
    bottomF6 := bottomF6
    bottomG5 := bottomG5
    rightF9 := rightPair.1
    rightG9 := rightPair.2
    southeastGCover := AuxiliaryCover.southeast_g_cover p hf
    northeastFCover := AuxiliaryCover.northeast_f_cover p hf
    northeastGCover := AuxiliaryCover.northeast_g_cover p hf
    northwestFCover := AuxiliaryCover.northwest_f_cover p hf
    northwestGCover := AuxiliaryCover.northwest_g_cover p hf
    topComponent := DirectDomains.top_component p hf }

theorem family_excluded : ExcludesFamily family :=
  family_excluded_of_auxiliary_entrance auxiliary_entrance

theorem case_excluded : ExcludesCase 1090 :=
  case_excluded_of_auxiliary_entrance auxiliary_entrance

end
#print axioms auxiliary_entrance
#print axioms family_excluded
#print axioms case_excluded
end N12Compact.Completion.OtherCases.C1090.OriginalData

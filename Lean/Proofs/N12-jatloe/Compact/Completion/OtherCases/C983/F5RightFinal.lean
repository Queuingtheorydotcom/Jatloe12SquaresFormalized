import Compact.Completion.OtherCases.C983.F5LowerRight
import Compact.Completion.OtherCases.InwardTwoBars

/-! Complete original-owner deletion of every F5 right component containing
both right auxiliaries. Its actual F8-to-F9 segment supplies the whole
foreign right bar, before the complete two-sign local ending is used. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_without_f8_check :
    ∀ owned∈f5SoutheastComponents,8∉owned → 4∈owned := by decide +kernel

theorem f5_right_not_both (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : ¬(8∈actual p 10 ∧ 9∈actual p 10) := by
  rintro ⟨rF8,rF9⟩
  have eF4 := southeast_without_f8_check _ (f5_southeast_components p hf f5)
    (absent_of_foreign p hf 10 5 8 (by decide +kernel) rF8)
  have west : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have upper : (owners p 7).Inside 2 (113/50) := by
    have h := auxiliary_inside p 7 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 5).Inside 2 (87/50) := by
    have h := auxiliary_inside p 5 4 (by decide +kernel) eF4
    simpa [auxPoints,fPoints,gPoints] using h
  have elbow : (owners p 5).Inside (113/50) 2 := by
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f5_southeast_g6 p hf f5)
    simpa [auxPoints,fPoints,gPoints] using h
  have rLower : (owners p 10).Inside 3 (87/50) := by
    have h := auxiliary_inside p 10 8 (by decide +kernel) rF8
    simpa [auxPoints,fPoints,gPoints] using h
  have rUpper : (owners p 10).Inside 3 (113/50) := by
    have h := auxiliary_inside p 10 9 (by decide +kernel) rF9
    simpa [auxPoints,fPoints,gPoints] using h
  apply InwardTwoBars.impossible ((owners p 7).translated 2 2)
    ((owners p 5).translated 2 2) (owners_side p 5) (owners_same_side p 7 5)
  · norm_num [inside_translated_iff]
    exact west
  · norm_num [inside_translated_iff]
    exact f5_merged_center p hf f5
  · norm_num [inside_translated_iff]
    exact upper
  · norm_num [inside_translated_iff]
    exact marker
  · norm_num [inside_translated_iff]
    exact inner
  · norm_num [inside_translated_iff]
    exact elbow
  · intro x low high own
    rw [inside_translated_iff] at own
    norm_num at own
    exact owners_apart p hf 5 9 (by decide +kernel) _ _
      ⟨own,bottom_bar p hf (2+x) (by linarith only [low]) (by linarith only [high])⟩
  · intro y low high own
    rw [inside_translated_iff] at own
    norm_num at own
    have foreign := CommonCases.OriginalOwners.vertical_segment (owners p 10) 3
      (87/50) (113/50) (2+y) rLower rUpper (by norm_num)
      (by linarith only [low]) (by linarith only [high])
    exact owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨own,foreign⟩
  · intro x y own
    exact owners_apart p hf 7 5 (by decide +kernel) (2+x) (2+y)
      ⟨(inside_translated_iff _ 2 2 x y).mp own.1,
        (inside_translated_iff _ 2 2 x y).mp own.2⟩

private theorem right_final_check :
    ∀ owned∈f5RightComponents,owned≠{8,18} → ¬(8∈owned ∧ 9∈owned) →
      owned={9,19} := by decide +kernel

theorem f5_right_final (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : actual p 10={9,19} :=
  right_final_check _ (f5_right_components p hf f5)
    (f5_right_not_lower p hf f5) (f5_right_not_both p hf f5)

def f5FinalSoutheast : List (Finset Nat) :=
  [{4,16},{4,16,18},{8,16},{8,16,18},{4,8,16},{4,8,16,18}]

private theorem southeast_final_check :
    ∀ owned∈f5SoutheastComponents,9∉owned → owned∈f5FinalSoutheast := by decide +kernel

theorem f5_final_central (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    actual p 5∈f5FinalSoutheast ∧ actual p 6={7,17} ∧
      actual p 10={9,19} ∧ actual p 11={3,14} := by
  have right := f5_right_final p hf f5
  have rF9 : 9∈actual p 10 := by rw [right]; decide +kernel
  have rG9 : 19∈actual p 10 := by rw [right]; decide +kernel
  have upper := f5_upper_of_right_g9 p hf f5 rG9
  exact ⟨southeast_final_check _ (f5_southeast_components p hf f5)
    (absent_of_foreign p hf 10 5 9 (by decide +kernel) rF9),upper.1,right,upper.2⟩

end
#print axioms f5_right_not_both
#print axioms f5_final_central
end N12Compact.Completion.OtherCases.C983


import Compact.Completion.OtherCases.C983.LeftOrigin
import Compact.Completion.OtherCases.PositiveEnding
import Compact.Completion.OtherCases.InwardSign

/-! Whole original-owner sign reduction after the F5 upper-right entrance.
The F8 branch uses the complete positive ending with the actual two bars;
the branch omitting F8 uses the earlier full inward-sign theorem. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_inward_check :
    ∀ owned∈f5FinalSoutheast,8∉owned → 4∈owned := by decide +kernel

theorem f5_negative_frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    ∃ E : OpenSquare,0<E.c ∧ E.s<0 ∧ -E.s≤E.c ∧ E.side=(owners p 5).side ∧
      (∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2)) := by
  obtain ⟨E,cp,range,shape,physical,_⟩ := ClosedFrames.canonical_frame ((owners p 5).translated 2 2)
  have physicalOriginal : ∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2) := by
    intro x y
    simpa only [inside_translated_iff,add_comm] using physical x y
  have side : 1<E.side := by simpa only [shape,OpenSquare.translated] using owners_side p 5
  have same : ((owners p 7).translated 2 2).side=E.side := by
    rw [shape]
    exact owners_same_side p 7 5
  have west : ((owners p 7).translated 2 2).Inside (-7/20) (-7/20) := by
    norm_num [inside_translated_iff]
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have center : ((owners p 7).translated 2 2).Inside 0 0 := by
    norm_num [inside_translated_iff]
    exact f5_merged_center p hf f5
  have upperInward : ((owners p 7).translated 2 2).Inside 0 (13/50) := by
    norm_num [inside_translated_iff]
    have h := auxiliary_inside p 7 5 (by decide +kernel) f5
    simpa [auxPoints,fPoints,gPoints] using h
  have marker : E.Inside (7/20) (-7/20) := by
    apply (physicalOriginal _ _).mpr
    norm_num
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : E.Inside (13/50) 0 := by
    apply (physicalOriginal _ _).mpr
    norm_num
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f5_southeast_g6 p hf f5)
    simpa [auxPoints,fPoints,gPoints] using h
  have bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1) := by
    intro x low high own
    have original := (physicalOriginal _ _).mp own
    norm_num at original
    exact owners_apart p hf 5 9 (by decide +kernel) _ _
      ⟨original,bottom_bar p hf (x+2) (by linarith only [low]) (by linarith only [high])⟩
  have left : ∀ y : ℝ,0≤y → y≤4/5 → ¬((owners p 7).translated 2 2).Inside (-1) y := by
    intro y low high own
    have original : (owners p 7).Inside 1 (y+2) := by
      simpa only [inside_translated_iff,show (2:ℝ)+ -1=1 by norm_num,add_comm] using own
    exact owners_apart p hf 7 8 (by decide +kernel) _ _
      ⟨original,f5_left_full_bar p hf f5 (y+2) (by linarith only [low]) (by linarith only [high])⟩
  have apart : ∀ x y,¬(((owners p 7).translated 2 2).Inside x y ∧ E.Inside x y) := by
    intro x y own
    exact owners_apart p hf 7 5 (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp own.1,by simpa only [add_comm] using (physicalOriginal _ _).mp own.2⟩
  have negative : E.s<0 := by
    apply lt_of_not_ge
    intro sign
    have order : E.s≤E.c := (abs_le.mp range).2
    by_cases f8 : 8∈actual p 5
    · have outer : E.Inside 1 (-13/50) := by
        apply (physicalOriginal _ _).mpr
        norm_num
        have h := auxiliary_inside p 5 8 (by decide +kernel) f8
        simpa [auxPoints,fPoints,gPoints] using h
      have points := f5_top_only_points p hf f5
      have missingOrigin : ¬E.Inside 1 0 := by
        intro own
        have original := (physicalOriginal _ _).mp own
        norm_num at original
        exact owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨original,points.2.2.2⟩
      have missingSharp : ¬E.Inside (21/40) (1/8) := by
        intro own
        have original := (physicalOriginal _ _).mp own
        norm_num at original
        exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨original,points.1⟩
      exact PositiveEnding.nonnegative_impossible ((owners p 7).translated 2 2) E side same
        (owners_cap p 7) cp sign order west center marker elbow outer missingOrigin missingSharp
        bottom left apart
    · have f4 := southeast_inward_check _ (f5_final_central p hf f5).1 f8
      have inner : E.Inside 0 (-13/50) := by
        apply (physicalOriginal _ _).mpr
        norm_num
        have h := auxiliary_inside p 5 4 (by decide +kernel) f4
        simpa [auxPoints,fPoints,gPoints] using h
      have missingF : ¬E.Inside 1 (-13/50) := by
        intro own
        have original := (physicalOriginal _ _).mp own
        norm_num at original
        have omitted := missing_auxiliary p 5 8 (by decide +kernel) f8
        have point : ¬(owners p 5).Inside 3 (87/50) := by
          simpa [auxPoints,fPoints,gPoints] using omitted
        exact point original
      exact InwardSign.positive_impossible ((owners p 7).translated 2 2) E side same cp sign order
        west center upperInward marker inner elbow missingF bottom apart
  exact ⟨E,cp,negative,by simpa only [abs_of_neg negative] using range,shape,physicalOriginal⟩

end
#print axioms f5_negative_frame
end N12Compact.Completion.OtherCases.C983

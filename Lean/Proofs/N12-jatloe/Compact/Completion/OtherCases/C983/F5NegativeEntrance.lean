import Compact.Completion.OtherCases.C983.F5NegativeFrame
import Compact.Completion.OtherCases.NegativeTripleFaces
import Compact.Completion.OtherCases.TopOnlyQuadrantScalars

/-! Full original-owner entrance for the last negative southeast/right
triple. This supplies actual frames and their entire faces; it is not an
assertion of the still-unproved three-square ending. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f5_negative_entrance (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) :
    ∃ E N : OpenSquare,
      E.side=(owners p 5).side ∧ N.side=(owners p 6).side ∧
      (∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2)) ∧
      (∀ x y,N.Inside x y ↔ (owners p 6).Inside (x+2) (y+2)) ∧
      NegativeTripleFaces.Data E (-E.s) ∧ TopOnlyQuadrantProfile.Data N ∧
      N.Inside 0 (31/50) ∧ N.Inside (1/2) 1 := by
  obtain ⟨E,cp,sn,order,shape,physical⟩ := f5_negative_frame p hf f5
  have final := f5_final_central p hf f5
  have g7 : 17∈actual p 6 := by rw [final.2.1]; decide +kernel
  have noF5 := absent_of_foreign p hf 7 6 5 (by decide +kernel) f5
  have points := f5_top_only_points p hf f5
  obtain ⟨N,nShape,nPhysical,nProfile,nLeft⟩ := northeast_quadrant_profile p hf g7 noF5
    points.1 (f5_top_origin p hf f5) (f5_right_bar p hf f5)
  have marker : E.Inside (7/20) (-7/20) := by
    apply (physical _ _).mpr
    norm_num
    have h := seed_inside p hf 5 (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have elbow : E.Inside (13/50) 0 := by
    apply (physical _ _).mpr
    norm_num
    have h := auxiliary_inside p 5 16 (by decide +kernel) (f5_southeast_g6 p hf f5)
    simpa [auxPoints,fPoints,gPoints] using h
  have missingCenter : ¬E.Inside 0 0 := by
    intro own
    have original := (physical _ _).mp own
    norm_num at original
    exact owners_apart p hf 5 7 (by decide +kernel) _ _
      ⟨original,f5_merged_center p hf f5⟩
  have missingOrigin : ¬E.Inside 1 0 := by
    intro own
    have original := (physical _ _).mp own
    norm_num at original
    exact owners_apart p hf 5 10 (by decide +kernel) _ _ ⟨original,points.2.2.2⟩
  have missingSharp : ¬E.Inside (21/40) (1/8) := by
    intro own
    have original := (physical _ _).mp own
    norm_num at original
    exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨original,points.1⟩
  have bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1) := by
    intro x low high own
    have original := (physical _ _).mp own
    norm_num at original
    exact owners_apart p hf 5 9 (by decide +kernel) _ _
      ⟨original,bottom_bar p hf (x+2) (by linarith only [low]) (by linarith only [high])⟩
  have eProfile := NegativeTripleFaces.faces E (-E.s) (by ring)
    (by simpa only [shape] using owners_side p 5) cp (by linarith only [sn]) order
    marker elbow missingCenter missingOrigin missingSharp bottom
  have nTop : N.Inside (1/2) 1 := by
    apply (nPhysical _ _).mpr
    norm_num
    exact points.2.1
  exact ⟨E,N,shape,nShape,physical,nPhysical,eProfile,nProfile,nLeft,nTop⟩

end
#print axioms f5_negative_entrance
end N12Compact.Completion.OtherCases.C983

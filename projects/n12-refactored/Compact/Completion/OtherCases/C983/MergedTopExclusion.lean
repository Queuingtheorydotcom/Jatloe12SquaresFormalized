import Compact.Completion.OtherCases.C983.ActualBars
import Compact.Completion.OtherCases.MergedTopExclusion

/-! The actual merged western owner cannot reach F3. Both foreign
objects are supplied by their original owners, including the entire
same-owner left segment. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem merged_no_f3 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    3∉actual p 7 := by
  intro f3
  have marker : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have top : (owners p 7).Inside (8/5) 3 := by
    have h := auxiliary_inside p 7 3 (by decide +kernel) f3
    simpa [auxPoints,fPoints,gPoints] using h
  have northeast : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  apply MergedTopExclusion.impossible (owners p 7) (owners_side p 7) (owners_cap p 7)
    marker top
  · exact fun own => owners_apart p hf 7 6 (by decide +kernel) _ _ ⟨own,northeast⟩
  · intro y low high own
    have foreign := left_bar p hf y low (by linarith only [high])
    exact owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨own,foreign⟩

end
#print axioms merged_no_f3
end N12Compact.Completion.OtherCases.C983


import Compact.Completion.OtherCases.C983.ActualOutwardPair

/-! Complete elimination of G6 from the actual merged C983 owner.
All possible original southeast components are retained until their full
actual-square obstruction is invoked; no preliminary merged catalogue is used. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem southeast_outward_check :
    ∀ owned∈originalComponents 5,16∉owned → (4∈owned ∨ 8∈owned) ∧ 18∈owned := by
  decide +kernel
private theorem right_forced_check :
    ∀ owned∈originalComponents 10,8∉owned → 9∈owned ∧ 19∈owned := by decide +kernel
private theorem northeast_forced_check :
    ∀ owned∈originalComponents 6,16∉owned → 9∉owned → 19∉owned → 13∉owned →
      17∈owned ∧ (5∈owned ∨ 7∈owned) := by decide +kernel
private theorem top_leftward_check :
    ∀ owned∈originalComponents 11,17∉owned → 3∈owned := by decide +kernel

theorem merged_no_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    16∉actual p 7 := by
  intro mergedG6
  have noG6 := absent_of_foreign p hf 7 5 16 (by decide +kernel) mergedG6
  have outward := southeast_outward_check _ (original_actual_mem p hf 5) noG6
  have noF4 : 4∉actual p 5 :=
    fun own => southeast_inward_outward_exclusion p hf own outward.2 noG6
  have f8 := outward.1.resolve_left noF4
  have right := right_forced_check _ (original_actual_mem p hf 10)
    (absent_of_foreign p hf 5 10 8 (by decide +kernel) f8)
  have northeast := northeast_forced_check _ (original_actual_mem p hf 6)
    (absent_of_foreign p hf 7 6 16 (by decide +kernel) mergedG6)
    (absent_of_foreign p hf 10 6 9 (by decide +kernel) right.1)
    (absent_of_foreign p hf 10 6 19 (by decide +kernel) right.2)
    (absent_of_foreign p hf 7 6 13 (by decide +kernel) (merged_g3 p hf))
  have topF3 := top_leftward_check _ (original_actual_mem p hf 11)
    (absent_of_foreign p hf 6 11 17 (by decide +kernel) northeast.1)
  have topOrigin := top_origin_of_f3 p hf topF3
  by_cases nF5 : 5∈actual p 6
  · exact southeast_outward_pair_exclusion p hf f8 outward.2 noG6 nF5 northeast.1 topOrigin
  · have nF7 := northeast.2.resolve_left nF5
    have lower := southeast_outward_point p hf f8 outward.2 noG6
    have upper := northeast_upper_point p hf nF7 nF5 topOrigin
      (right_bar_of_f8 p hf f8 right.1 right.2)
    exact owners_apart p hf 5 6 (by decide +kernel) _ _ ⟨lower,upper⟩

end
#print axioms merged_no_g6
end N12Compact.Completion.OtherCases.C983


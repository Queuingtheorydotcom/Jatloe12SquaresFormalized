import Compact.Completion.OtherCases.C983.F4UniformProfile
import Compact.Completion.OtherCases.C983.F4OuterMidpointOriginal
import Compact.Completion.OtherCases.C983.F5Completion
import Compact.Completion.OtherCases.C983.ThreeBranches

/-! Complete original-owner composition of the supplied C983 F4 ending.
The strict singleton seeds, merged center, right origin and southeast
profile are all produced above from the actual family. The two midpoints
are distinct statements: Q9 excludes (2,1.5), while Q5 owns (3,1.5).
The new source is uncompiled; this is not a kernel acceptance receipt. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

theorem f4_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : False := by
  by_cases f5 : 5∈actual p 7
  · exact f5_impossible p hf f5
  · obtain ⟨E,t,shape,physical,data,half,lowerU⟩ := f4_southeast_profile p hf f4
    have seeds := f4_bottom_singleton_seeds p hf f4
    have middle := f4_bottom_midpoint_excluded_of_frame p hf f4 E t shape physical
      data seeds.2.2
    have outer := f4_outer_midpoint_of_frame p hf f4 f5 (f4_merged_center p hf f4)
      E t shape physical data half lowerU
    have origin := bottom_origin_of_southeast_outer p hf outer
    exact C974LocalEnding.bottom_missing_corner_excluded_of_seeds p hf
      seeds.1 seeds.2.1 seeds.2.2 origin middle outer

theorem family_impossible : ExcludesFamily family := by
  intro p hf
  have components := merged_three_branches p hf
  have cover : ∀ owned∈mergedFinalComponents,4∈owned ∨ 5∈owned := by decide +kernel
  rcases cover _ components with f4 | f5
  · exact f4_impossible p hf f4
  · exact f5_impossible p hf f5

theorem case_excluded : ExcludesCase 983 := excludes_case family_impossible

end
#print axioms f4_impossible
#print axioms family_impossible
#print axioms case_excluded
end N12Compact.Completion.OtherCases.C983

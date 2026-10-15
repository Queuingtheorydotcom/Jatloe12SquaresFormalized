import Compact.Completion.C981.Common107

/-! Reuse the common-cycle geometry for five additional original rows.
The finite entrance checks retain all actual owners and missing points;
additional auxiliary ownership is harmless only where these checks say so.

This source candidate still requires serial replay together with Common107.
It is deliberately not registered as accepted progress before that replay. -/
namespace N12Compact.C981CompletionNewSimpleShortRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def transposedIds : List Nat := [54,56,58,109]

theorem transposed_checked :
    ∀ i ∈ transposedIds, C981CompletionCommon107.Check (representativeVectors[i]!) := by
  decide +kernel

theorem checked73 : C981CompletionCommonRows.Check (representativeVectors[73]!) := by
  decide +kernel

def coveredIds : List Nat := [54,56,58,73,109]

theorem covered_excluded (i : Nat) (member : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := by
  by_cases h : i = 73
  · subst i
    exact C981CompletionCommonRows.excludes _ checked73
  · have transposed : i ∈ transposedIds := by
      simpa only [coveredIds,transposedIds,List.mem_cons,List.not_mem_nil,or_false,h,
        false_or] using member
    exact C981CompletionCommon107.excludes _ (transposed_checked i transposed)

#print axioms covered_excluded
end N12Compact.C981CompletionNewSimpleShortRows

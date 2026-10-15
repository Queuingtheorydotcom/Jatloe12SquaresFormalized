import Compact.Completion.OtherCases.MergedPending.C700FullCornerSingleton
import Compact.Completion.OtherCases.MergedPending.C700LeftCornerSingleton
import Compact.Assembly.RowIdentity

/-! Complete original C700 exclusion. Two applications of the shared
three-square missing-corner theorem force the distinct actual singletons
1 and 2 to contain (1,1) strictly. Every angle and boundary alternative is
retained by those theorems. No central orientation premise is needed.
This source has not been compiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot S12Completion CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem family700_excluded : ExcludesFamily (family .c700) := by
  intro p hf
  exact apart _ p hf 1 2 (by decide +kernel) (by decide +kernel) (by decide)
    1 1 ⟨c700_bottom_singleton_corner p hf,c700_left_singleton_corner p hf⟩

private theorem lookup700 :
    (N12Compact.RowIdentity.rowAt 381).originalId=700 ∧
      (N12Compact.RowIdentity.rowAt 381).groups=family .c700 := by decide +kernel

theorem row700_family : ∀ r∈retainedRows,r.originalId=700 → r.groups=family .c700 :=
  N12Compact.RowIdentity.family_at 381 700 (family .c700) lookup700

theorem case700_excluded : ExcludesCase 700 := by
  intro r member identity
  simpa only [row700_family r member identity] using family700_excluded

end
#print axioms family700_excluded
#print axioms case700_excluded
end N12Compact.MergedPending

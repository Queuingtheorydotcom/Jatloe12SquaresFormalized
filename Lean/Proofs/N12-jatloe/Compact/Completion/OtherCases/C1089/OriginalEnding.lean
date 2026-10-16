import Compact.Completion.OtherCases.C1089.AllPositive
import Compact.Completion.OtherCases.C1089.SectorEndings
import Compact.Completion.OtherCases.C1089.ReverseStructural
import Compact.Completion.OtherCases.C1089.LastActual
import Compact.Assembly.RowIdentity

/-! The original C1089 family and retained row573, joined through all
closed wall-center sectors. Every finite auxiliary premise is supplied
by existing compact local certificates at the actual family budgets;
all continuous producers retain their named actual owners. Q0 is the
true singleton1 and marker1 remains absent everywhere. No catalogue,
square-angle choice or stronger singleton seed is assumed. Source only:
this new family/row proof has not been compiled or replayed. -/
namespace N12Compact.Completion.OtherCases.C1089.OriginalData
open S12 S12Pilot S12Completion
set_option Elab.async false

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  by_cases left : 2≤centerY (owners p 8)
  · by_cases right : 2≤centerY (owners p 10)
    · by_cases top : 2≤centerX (owners p 11)
      · exact AllPositive.impossible p hf left right top
      · exact SectorEntrances.mmmp_impossible p hf left right (le_of_not_ge top)
    · by_cases top : 2≤centerX (owners p 11)
      · exact LastActual.impossible p hf (le_of_not_ge right) top
      · exact SectorEndings.opposed_impossible p hf left (le_of_not_ge right)
          (le_of_not_ge top)
  · by_cases right : 2≤centerY (owners p 10)
    · by_cases top : 2≤centerX (owners p 11)
      · exact SectorEndings.northeast_inward_impossible p hf (le_of_not_ge left) right top
      · exact Reverse.impossible p hf (le_of_not_ge left) (le_of_not_ge top)
    · exact WallCore.two_low_impossible p hf (le_of_not_ge left) (le_of_not_ge right)

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 573).originalId=1089 ∧
      (N12Compact.RowIdentity.rowAt 573).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=1089 → r.groups=family :=
  N12Compact.RowIdentity.family_at 573 1089 family lookup

theorem case_excluded : ExcludesCase 1089 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms family_excluded
#print axioms row_family
#print axioms case_excluded
end N12Compact.Completion.OtherCases.C1089.OriginalData

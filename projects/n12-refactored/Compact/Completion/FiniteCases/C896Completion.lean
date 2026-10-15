import Compact.Completion.FiniteCases.C896Centers
import Compact.Assembly.RowIdentity

/-! Original C896 family and retained-row483 source contracts.
All orientations and optional G ownerships are preserved by the
actual-center contradiction. This source has not been compiled. -/
namespace N12Compact.FiniteCases.C896Ending
open S12 S12Completion C896Domains
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 483).originalId=896 ∧
      (N12Compact.RowIdentity.rowAt 483).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=896 → r.groups=family :=
  N12Compact.RowIdentity.family_at 483 896 family lookup

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  exact impossible p hf

theorem case_excluded : ExcludesCase 896 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms family_excluded
#print axioms case_excluded
end N12Compact.FiniteCases.C896Ending

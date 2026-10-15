import Compact.Completion.OtherCases.C974.ActualEnding
import Compact.Assembly.RowIdentity

/-! C974 original-family and retained-row505 contracts. These are source
proofs awaiting compilation; no Lean acceptance receipt is asserted. -/
namespace N12Compact.Completion.OtherCases.C974.OriginalData
open S12 S12Completion
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 505).originalId=974 ∧
      (N12Compact.RowIdentity.rowAt 505).groups=family := by decide +kernel
theorem row_family : ∀ r∈retainedRows,r.originalId=974 → r.groups=family :=
  N12Compact.RowIdentity.family_at 505 974 family lookup
theorem family_excluded : ExcludesFamily family := by
  intro p hf
  exact impossible p hf
theorem case_excluded : ExcludesCase 974 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms family_excluded
#print axioms case_excluded
end N12Compact.Completion.OtherCases.C974.OriginalData

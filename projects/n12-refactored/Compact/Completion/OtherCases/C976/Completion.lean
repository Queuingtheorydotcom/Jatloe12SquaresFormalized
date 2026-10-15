import Compact.Completion.OtherCases.C976.ActualEnding
import Compact.Assembly.RowIdentity

/-! Original C976 family and retained-row507 adapter. Every geometric
premise is produced from the actual family in ActualEnding. The existing
local certificate and retained-row trust is inherited; there are no new
native sites, axioms or admissions. These new declarations are source
proofs awaiting compilation, not a claimed Lean acceptance receipt. -/
namespace N12Compact.Completion.OtherCases.C976.OriginalData
open S12 S12Completion
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 507).originalId=976 ∧
      (N12Compact.RowIdentity.rowAt 507).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=976 → r.groups=family :=
  N12Compact.RowIdentity.family_at 507 976 family lookup

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  exact impossible p hf

theorem case_excluded : ExcludesCase 976 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms family_excluded
#print axioms case_excluded
end N12Compact.Completion.OtherCases.C976.OriginalData

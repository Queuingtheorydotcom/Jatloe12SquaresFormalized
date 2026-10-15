import Compact.Completion.FiniteCases.C975Ending
import Compact.Assembly.RowIdentity

/-! C975 original-family and retained-row506 contracts. The complete
actual-owner source proof is separate from future Lean compilation;
no kernel acceptance or replay receipt is asserted here. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Completion C975Domains
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 506).originalId=975 ∧
      (N12Compact.RowIdentity.rowAt 506).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=975 → r.groups=family :=
  N12Compact.RowIdentity.family_at 506 975 family lookup

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  exact impossible p hf

theorem case_excluded : ExcludesCase 975 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms family_excluded
#print axioms case_excluded
end N12Compact.FiniteCases.C975Selection

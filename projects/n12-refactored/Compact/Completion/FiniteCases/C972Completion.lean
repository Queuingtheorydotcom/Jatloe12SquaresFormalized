import Compact.Completion.FiniteCases.C972NortheastPositiveEnding
import Compact.Assembly.RowIdentity

/-! Original C972 family and retained-row503 source contracts. The actual
owner entrance and every geometric branch precede this row adapter.
Compilation and the eventual complete replay remain separate obligations. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Completion
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 503).originalId=972 ∧
      (N12Compact.RowIdentity.rowAt 503).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=972 → r.groups=family :=
  N12Compact.RowIdentity.family_at 503 972 family lookup

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  exact family_impossible p hf

theorem case_excluded : ExcludesCase 972 := by
  intro r member identity
  simpa only [row_family r member identity] using family_excluded

#print axioms family_excluded
#print axioms case_excluded
end N12Compact.FiniteCases.C972

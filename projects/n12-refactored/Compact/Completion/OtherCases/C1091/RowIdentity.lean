import Compact.Assembly.RowIdentity
import Compact.Completion.OtherCases.C1091.ResidualProduction

/-! Original row575 is bound to the literal C1091 family. The final
contract remains conditional on the six raw entrance points: the
unavailable earlier sector proof is not replaced by an assertion or axiom.
No original-case registry is changed. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1091.OriginalData
open S12 S12Completion
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 575).originalId=1091 ∧
      (N12Compact.RowIdentity.rowAt 575).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=1091 → r.groups=family :=
  N12Compact.RowIdentity.family_at 575 1091 family lookup

theorem excludes_case (h : ExcludesFamily family) : ExcludesCase 1091 := by
  intro r member identity
  simpa only [row_family r member identity] using h

theorem family_excluded_of_residual_entrance
    (produce : ∀ p : NormalizedPacking,codedMarkerFamily p=family →
      ResidualEntrance (owners p)) : ExcludesFamily family := by
  intro p hf
  exact impossible_of_residual_entrance p hf (produce p hf)

theorem case_excluded_of_residual_entrance
    (produce : ∀ p : NormalizedPacking,codedMarkerFamily p=family →
      ResidualEntrance (owners p)) : ExcludesCase 1091 :=
  excludes_case (family_excluded_of_residual_entrance produce)

#print axioms row_family
#print axioms case_excluded_of_residual_entrance
end N12Compact.Completion.OtherCases.C1091.OriginalData

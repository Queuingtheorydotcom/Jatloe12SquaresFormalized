import Compact.Assembly.RowIdentity
import Compact.Completion.OtherCases.C1090.OriginalEnding

/-! The actual C1090 row/family identity and conditional final adapter.
The row is position574 in the unchanged577-row original CoverData. This
source checks its literal family; it does not rely on the unprovided JSON
identity extraction linked by the new prose. The missing finite producer
remains an explicit parameter, so no original-case registry is changed.
The inherited retained-row identity proof keeps its existing native
certificate dependency. No new native site is introduced. Uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.OriginalData
open S12 S12Completion
set_option Elab.async false

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 574).originalId=1090 ∧
      (N12Compact.RowIdentity.rowAt 574).groups=family := by decide +kernel

theorem row_family : ∀ r∈retainedRows,r.originalId=1090 → r.groups=family :=
  N12Compact.RowIdentity.family_at 574 1090 family lookup

theorem excludes_case (h : ExcludesFamily family) : ExcludesCase 1090 := by
  intro r member identity
  simpa only [row_family r member identity] using h

/-- This is the precise original-packing producer still to be supplied.
Its result contains only the thirteen finite auxiliary consequences in
AuxiliaryEntrance; every later geometric step is already written. -/
theorem family_excluded_of_auxiliary_entrance
    (produce : ∀ p : NormalizedPacking,codedMarkerFamily p=family →
      AuxiliaryEntrance (owners p)) : ExcludesFamily family := by
  intro p hf
  exact impossible_of_auxiliary_entrance p hf (produce p hf)

theorem case_excluded_of_auxiliary_entrance
    (produce : ∀ p : NormalizedPacking,codedMarkerFamily p=family →
      AuxiliaryEntrance (owners p)) : ExcludesCase 1090 :=
  excludes_case (family_excluded_of_auxiliary_entrance produce)

#print axioms row_family
#print axioms case_excluded_of_auxiliary_entrance
end N12Compact.Completion.OtherCases.C1090.OriginalData

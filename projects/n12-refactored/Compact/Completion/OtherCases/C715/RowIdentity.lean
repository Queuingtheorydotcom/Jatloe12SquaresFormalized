import Compact.Assembly.RowIdentity

namespace N12Compact.Completion.OtherCases.C715
open S12 S12Completion
set_option Elab.async false

def family : Finset Nat :=
  {1,2,12,16,32,192,512,2304,4096,8192,17408,32768}

def ownerCode : Fin 12 → Nat :=
  ![1,2,12,16,32,192,512,2304,4096,8192,17408,32768]

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 396).originalId = 715 ∧
    (N12Compact.RowIdentity.rowAt 396).groups = family := by
  decide +kernel

theorem row_family : ∀ r ∈ retainedRows, r.originalId = 715 → r.groups = family :=
  N12Compact.RowIdentity.family_at 396 715 family lookup

theorem excludes_case (h : ExcludesFamily family) : ExcludesCase 715 := by
  intro r hr hid
  simpa only [row_family r hr hid] using h

end N12Compact.Completion.OtherCases.C715

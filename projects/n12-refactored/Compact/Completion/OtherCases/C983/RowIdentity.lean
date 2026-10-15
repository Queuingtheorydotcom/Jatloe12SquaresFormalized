import Compact.Assembly.RowIdentity

namespace N12Compact.Completion.OtherCases.C983
open S12 S12Completion
set_option Elab.async false

def family : Finset Nat := {1,2,12,48,192,512,1024,2304,4096,8192,16384,32768}

def ownerCode : Fin 12 → Nat :=
  ![1,2,12,48,192,512,1024,2304,4096,8192,16384,32768]

private theorem lookup :
    (N12Compact.RowIdentity.rowAt 514).originalId=983 ∧
      (N12Compact.RowIdentity.rowAt 514).groups=family := by decide +kernel

theorem row_family :
    ∀ r∈retainedRows,r.originalId=983 → r.groups=family :=
  N12Compact.RowIdentity.family_at 514 983 family lookup

theorem excludes_case (h : ExcludesFamily family) : ExcludesCase 983 := by
  intro r member identity
  simpa only [row_family r member identity] using h

end N12Compact.Completion.OtherCases.C983


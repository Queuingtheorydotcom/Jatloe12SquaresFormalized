import Compact.Assembly.RowIdentity

namespace N12Compact.Completion.OtherCases.C705716
open S12 S12Completion
set_option Elab.async false

/-- False denotes C705; true denotes C716. These are the unchanged original
families, with the three-marker central owner kept as one physical square. -/
def family (b : Bool) : Finset Nat :=
  if b then {1,2,12,16,32,192,512,3328,4096,8192,16384,32768}
  else {1,2,12,16,32,192,256,3584,4096,8192,16384,32768}

def caseId (b : Bool) : Nat := if b then 716 else 705

def ownerCode (b : Bool) : Fin 12 → Nat :=
  ![1,2,12,16,32,192,(if b then 512 else 256),
    (if b then 3328 else 3584),4096,8192,16384,32768]

private theorem lookup (b : Bool) :
    (N12Compact.RowIdentity.rowAt (if b then 397 else 386)).originalId = caseId b ∧
    (N12Compact.RowIdentity.rowAt (if b then 397 else 386)).groups = family b := by
  cases b <;> decide +kernel

theorem row_family (b : Bool) :
    ∀ r ∈ retainedRows, r.originalId = caseId b → r.groups = family b :=
  N12Compact.RowIdentity.family_at (if b then 397 else 386) (caseId b) (family b) (lookup b)

theorem excludes_case (b : Bool) (h : ExcludesFamily (family b)) : ExcludesCase (caseId b) := by
  intro r hr hid
  simpa only [row_family b r hr hid] using h

end N12Compact.Completion.OtherCases.C705716

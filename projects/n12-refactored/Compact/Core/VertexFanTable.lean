import Compact.Core.CachedSupportFan

/-!
A compact checked table interface for cached support fans. A data row describes
one context and its vertices; one finite check certifies its row memberships
and exact vertex identities. Certification does not assert that a fan covers
any direction. Every later pair check still verifies its actual eight axes.
-/
namespace N12Compact.VertexFanTable
open IntegerSupport CachedSupportFan

structure RawContext (r : Nat) where
  inputs : List (Fin r)
  reference : ReferenceAxis.Reference
  entries : Array (Entry r)

def RawContext.Check {r : Nat} (rows : Fin r → Row) (context : RawContext r) : Prop :=
  0 < context.entries.size ∧
    ∀ i : Fin context.entries.size, (context.entries[i.val]'i.isLt).Check rows context.inputs

instance {r : Nat} (rows : Fin r → Row) (context : RawContext r) :
    Decidable (context.Check rows) := inferInstanceAs (Decidable (_ ∧ _))

/-- All semantic evidence comes from `checked`; data never supplies a proof. -/
def RawContext.certify {r : Nat} (rows : Fin r → Row) (context : RawContext r)
    (checked : context.Check rows) : Context rows where
  inputs := context.inputs
  reference := context.reference
  fallback := ⟨context.entries[0]'checked.1, checked.2 ⟨0, checked.1⟩⟩
  entries := Array.ofFn fun i : Fin context.entries.size =>
    ⟨context.entries[i.val]'i.isLt, checked.2 i⟩

@[simp] theorem RawContext.certify_inputs {r : Nat} (rows : Fin r → Row)
    (context : RawContext r) (checked : context.Check rows) :
    (context.certify rows checked).inputs = context.inputs := rfl

@[simp] theorem RawContext.certify_reference {r : Nat} (rows : Fin r → Row)
    (context : RawContext r) (checked : context.Check rows) :
    (context.certify rows checked).reference = context.reference := rfl

end N12Compact.VertexFanTable

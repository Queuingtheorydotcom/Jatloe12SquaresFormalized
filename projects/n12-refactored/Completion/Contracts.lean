import S12.PackingConstant

/- Work directly in Jatloe's model and namespaces. No port or replacement
   geometry is introduced. This file is a proof interface, not a completion. -/
namespace S12Completion

def ExcludesFamily (family : Finset Nat) : Prop :=
  ∀ p : S12.NormalizedPacking, S12.codedMarkerFamily p = family → False

/-- A case worker must exclude every retained row with this historical ID.
    This includes the row/family identity; a certificate for an unrelated
    family, subregion, or fixed angle cannot satisfy the contract. -/
def ExcludesCase (id : Nat) : Prop :=
  ∀ r ∈ S12.retainedRows, r.originalId = id → ExcludesFamily r.groups

end S12Completion

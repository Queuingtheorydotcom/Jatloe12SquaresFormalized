import S12.CertifiedDomain
namespace S12
set_option maxHeartbeats 0

/-- Remove an auxiliary-owner value only when it has no disjoint value in
another owner's complete domain. The other domain need not be a singleton. -/
def CertifiedDomain.refineAgainst {family : Finset Nat}
    (a b : CertifiedDomain family) (hb : b.mask∈family) (hne : a.mask≠b.mask) :
    CertifiedDomain family :=
  ⟨a.mask,a.allowed.filter (fun x => decide (∃ y∈b.allowed,Disjoint x y)),by
    intro p i hf hi
    have hj : markerCode p (ownerIndex p b.mask)=b.mask :=
      ownerIndex_spec p b.mask (by rw [hf]; exact hb)
    apply List.mem_filter.mpr
    refine ⟨a.sound p i hf hi,decide_eq_true ?_⟩
    refine ⟨natCombinedOwners p (ownerIndex p b.mask),b.sound p _ hf hj,?_⟩
    apply nat_combined_disjoint
    intro he
    apply hne
    exact hi.symm.trans ((congrArg (markerCode p) he).trans hj)⟩

/-- A checked superset can simplify a certified domain without losing coverage. -/
def CertifiedDomain.enlarge {family : Finset Nat} (d : CertifiedDomain family)
    (allowed : List (Finset Nat)) (h : ∀ x∈d.allowed,x∈allowed) : CertifiedDomain family :=
  ⟨d.mask,allowed,fun p i hf hi => h _ (d.sound p i hf hi)⟩

#print axioms CertifiedDomain.refineAgainst
end S12

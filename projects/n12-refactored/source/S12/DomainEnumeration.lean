import S12.CertifiedDomain
namespace S12
set_option maxHeartbeats 0

/-- Enumerate whole auxiliary-ownership vectors. Overlap with earlier owners
is the only pruning rule here; no geometric or symmetry assumption is added. -/
def enumerateAssignments {P : Type} [DecidableEq P] :
    List (List (Finset P)) → Finset P → List (List (Finset P))
  | [],_ => [[]]
  | d::ds,used => d.flatMap (fun x =>
      if Disjoint x used then (enumerateAssignments ds (used∪x)).map (fun xs => x::xs) else [])

theorem enumerateAssignments_complete {P : Type} [DecidableEq P]
    (xs : List (Finset P)) (ds : List (List (Finset P))) (used : Finset P)
    (ha : List.Forall₂ (fun x d => x∈d) xs ds)
    (hu : ∀ x∈xs,Disjoint x used) (hp : xs.Pairwise Disjoint) :
    xs∈enumerateAssignments ds used := by
  induction ha generalizing used with
  | nil => simp [enumerateAssignments]
  | @cons x d xs ds hx hxs ih =>
    have hxu : Disjoint x used := hu x (by simp)
    have hpt := (List.pairwise_cons.mp hp).2
    have htail : xs∈enumerateAssignments ds (used∪x) := by
      apply ih _ ?_ hpt
      intro y hy
      apply Finset.disjoint_union_right.mpr
      exact ⟨hu y (by simp [hy]),((List.pairwise_cons.mp hp).1 y hy).symm⟩
    apply List.mem_flatMap.mpr
    refine ⟨x,hx,?_⟩
    rw [if_pos hxu]
    exact List.mem_map.mpr ⟨xs,htail,rfl⟩

/-- Every actual packing supplies one of the enumerated whole vectors. This
is the coverage interface needed when an owner has several possible F/G sets. -/
theorem certified_domain_assignments_mem {family : Finset Nat}
    (ds : List (CertifiedDomain family))
    (hmem : ∀ d∈ds,d.mask∈family) (hpair : ds.Pairwise (fun a b => a.mask≠b.mask))
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ds.map (fun d => natCombinedOwners p (ownerIndex p d.mask)) ∈
      enumerateAssignments (ds.map (fun d => d.allowed)) ∅ := by
  let actual := fun d : CertifiedDomain family => natCombinedOwners p (ownerIndex p d.mask)
  have hcode : ∀ d∈ds,markerCode p (ownerIndex p d.mask)=d.mask := by
    intro d hd
    apply ownerIndex_spec
    rw [hf]
    exact hmem d hd
  have ha : List.Forall₂ (fun x d => x∈d) (ds.map actual) (ds.map (fun d => d.allowed)) := by
    rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro d hd
    exact d.sound p _ hf (hcode d hd)
  have hp : (ds.map actual).Pairwise Disjoint := by
    rw [List.pairwise_map]
    apply (List.Pairwise.and_mem.mp hpair).imp
    intro a b h
    apply nat_combined_disjoint
    intro he
    exact h.2.2 ((hcode a h.1).symm.trans ((congrArg (markerCode p) he).trans (hcode b h.2.1)))
  exact enumerateAssignments_complete _ _ ∅ ha (by intros; exact Finset.disjoint_empty_right _) hp

def DomainCasesCheck {family : Finset Nat} (ds : List (CertifiedDomain family))
    (cases : List (List (Finset Nat))) : Prop :=
  ∀ a∈enumerateAssignments (ds.map (fun d => d.allowed)) ∅,a∈cases
instance decidableDomainCasesCheck {family : Finset Nat} (ds : List (CertifiedDomain family))
    (cases : List (List (Finset Nat))) : Decidable (DomainCasesCheck ds cases) :=
  inferInstanceAs (Decidable (∀ a∈_,_))

theorem domain_cases_sound {family : Finset Nat} (ds : List (CertifiedDomain family))
    (hmem : ∀ d∈ds,d.mask∈family) (hpair : ds.Pairwise (fun a b => a.mask≠b.mask))
    (cases : List (List (Finset Nat))) (hc : DomainCasesCheck ds cases)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ds.map (fun d => natCombinedOwners p (ownerIndex p d.mask))∈cases :=
  hc _ (certified_domain_assignments_mem ds hmem hpair p hf)

#print axioms domain_cases_sound
end S12

import S12.CertifiedDomain

/-! A finite ownership cover may force an auxiliary point without fixing the
owner's other auxiliary points. This keeps every permitted extra point. -/
namespace N12Compact.ForcedAuxiliary
open S12

def withoutPoint {family : Finset Nat} (ds : List (CertifiedDomain family))
    (mask index : Nat) : List (List (Finset Nat)) :=
  ds.map (fun d => if d.mask = mask then
    d.allowed.filter (fun x => decide (index ∉ x)) else d.allowed)

theorem contains {family : Finset Nat} (ds : List (CertifiedDomain family))
    (hmem : ∀ d ∈ ds, d.mask ∈ family)
    (hpair : ds.Pairwise (fun a b => a.mask ≠ b.mask))
    (mask index : Nat) (checked : feasible (withoutPoint ds mask index) ∅ = false)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    index ∈ natCombinedOwners p (ownerIndex p mask) := by
  classical
  by_contra absent
  let actual := fun d : CertifiedDomain family => natCombinedOwners p (ownerIndex p d.mask)
  have code : ∀ d ∈ ds, markerCode p (ownerIndex p d.mask) = d.mask := by
    intro d hd
    apply ownerIndex_spec
    rw [hf]
    exact hmem d hd
  have allowed : List.Forall₂ (fun x d => x ∈ d)
      (ds.map actual) (withoutPoint ds mask index) := by
    rw [withoutPoint,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro d hd
    split_ifs with same
    · apply List.mem_filter.mpr
      refine ⟨d.sound p _ hf (code d hd),decide_eq_true ?_⟩
      simpa only [actual,same] using absent
    · exact d.sound p _ hf (code d hd)
  have disjoint : (ds.map actual).Pairwise Disjoint := by
    rw [List.pairwise_map]
    apply (List.Pairwise.and_mem.mp hpair).imp
    intro a b h
    apply nat_combined_disjoint
    intro equal
    exact h.2.2 ((code a h.1).symm.trans
      ((congrArg (markerCode p) equal).trans (code b h.2.1)))
  exact rejected_domain_impossible _ checked
    (actual_owners_give_assignment _ _ ∅ allowed
      (by intros; exact Finset.disjoint_empty_right _) disjoint)

#print axioms contains
end N12Compact.ForcedAuxiliary

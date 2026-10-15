import S12.CoreExclusion
namespace S12
set_option maxHeartbeats 0

/-- A finite auxiliary ownership domain, with its geometric validity proved. -/
structure CertifiedDomain (family : Finset Nat) where
  mask : Nat
  allowed : List (Finset Nat)
  sound : ∀ (p : NormalizedPacking) (i : Fin 12),codedMarkerFamily p=family →
    markerCode p i=mask → natCombinedOwners p i∈allowed

def CertifiedDomain.ofCombined (family : Finset Nat) (w : CombinedSpec) (hw : w.Check)
    (hm : w.Matches family) : CertifiedDomain family :=
  ⟨w.mask,w.allowed,fun p i hf hi => w.actual hw family hm p i hf hi⟩

def CertifiedDomain.ofProduct (family : Finset Nat) (a b : SingleSpec)
    (ha : a.Check) (hb : b.Check) (hma : a.Matches family 0) (hmb : b.Matches family 1)
    (he : a.mask=b.mask) : CertifiedDomain family :=
  ⟨a.mask,a.allowed.flatMap (fun x => b.allowed.map (combinedOwners x)),by
    intro p i hf hi
    exact List.mem_flatMap.mpr ⟨_,a.actual ha family 0 hma p i hf hi,
      List.mem_map.mpr ⟨_,b.actual hb family 1 hmb p i hf (hi.trans he),rfl⟩⟩⟩

def CertifiedDomain.remove (family : Finset Nat) (d : CertifiedDomain family)
    (q : LocalQuery) (hq : q.Check) (hm : q.mask=d.mask) (hk : q.kind=2) : CertifiedDomain family :=
  ⟨d.mask,d.allowed.filter (fun x => decide (x≠q.owned)),by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨d.sound p i hf hi,decide_eq_true ?_⟩
    intro he
    exact q.sound hq (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one) (by rw [p.congruent]; exact p.side_le)
      (p.contained i) (by simpa only [hm,hi] using coded_exact p i)
      (by simpa only [hk,he] using nat_combined_exact p i)⟩

def forcedDomains {family : Finset Nat} (ds : List (CertifiedDomain family))
    (mask : Nat) (value : Finset Nat) : List (List (Finset Nat)) :=
  ds.map (fun d => if d.mask=mask then d.allowed.filter (fun x => decide (x≠value)) else d.allowed)

/-- Refuting all assignments that omit a proposed owner set proves it forced.
Only the finite solver is evaluated; its link to real packings is a theorem. -/
theorem certified_domain_forced {family : Finset Nat} (ds : List (CertifiedDomain family))
    (hmem : ∀ d∈ds,d.mask∈family) (hpair : ds.Pairwise (fun a b => a.mask≠b.mask))
    (mask : Nat) (value : Finset Nat) (hcheck : feasible (forcedDomains ds mask value) ∅=false)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    natCombinedOwners p (ownerIndex p mask)=value := by
  classical
  by_contra hn
  let actual := fun d : CertifiedDomain family => natCombinedOwners p (ownerIndex p d.mask)
  have hcode : ∀ d∈ds,markerCode p (ownerIndex p d.mask)=d.mask := by
    intro d hd
    apply ownerIndex_spec
    rw [hf]
    exact hmem d hd
  have hallowed : List.Forall₂ (fun x d => x∈d) (ds.map actual) (forcedDomains ds mask value) := by
    rw [forcedDomains,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro d hd
    split_ifs with he
    · apply List.mem_filter.mpr
      refine ⟨d.sound p _ hf (hcode d hd),decide_eq_true ?_⟩
      simpa only [actual,he] using hn
    · exact d.sound p _ hf (hcode d hd)
  have hdis : (ds.map actual).Pairwise Disjoint := by
    rw [List.pairwise_map]
    apply (List.Pairwise.and_mem.mp hpair).imp
    intro a b h
    apply nat_combined_disjoint
    intro he
    exact h.2.2 ((hcode a h.1).symm.trans ((congrArg (markerCode p) he).trans (hcode b h.2.1)))
  exact rejected_domain_impossible _ hcheck
    (actual_owners_give_assignment _ _ ∅ hallowed (by intros; exact Finset.disjoint_empty_right _) hdis)

#print axioms certified_domain_forced
end S12

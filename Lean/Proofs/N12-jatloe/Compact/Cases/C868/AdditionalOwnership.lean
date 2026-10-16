import Compact.Cases.C868.Ownership

/-! Further consequences of the same nine original C868 domains.  The
finite arguments retain every allowed auxiliary set, including extra G
points; they do not import the seven-row diagnostic as a certificate.
These are source proofs awaiting compilation. -/
namespace N12Compact.C868
open S12 S12Pilot
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

/-- The compulsory points needed for the actual neighbouring squares. -/
def additionalClaims : Fin 8 → Nat × Nat :=
  ![(16,7),(16,17),(4096,1),(4096,11),(8192,6),(8192,15),(32768,3),(512,8)]

theorem additionalClaims_checked (i : Fin 8) :
    feasible (ForcedAuxiliary.withoutPoint domains (additionalClaims i).1
      (additionalClaims i).2) ∅ = false := by
  fin_cases i <;> decide +kernel

theorem additional_inside (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 8) :
    (owner p (additionalClaims i).1).Inside
      ((auxPoints 2)[(additionalClaims i).2]!).1
      ((auxPoints 2)[(additionalClaims i).2]!).2 := by
  apply (nat_combined_exact p (ownerIndex p (additionalClaims i).1)
    (additionalClaims i).2 (by fin_cases i <;> decide +kernel)).mpr
  exact ForcedAuxiliary.contains domains domains_members domains_distinct
    (additionalClaims i).1 (additionalClaims i).2
    (additionalClaims_checked i) p hf

private def withoutSoutheastG : List (List (Finset Nat)) :=
  domains.map (fun d => if d.mask = 512 then
    d.allowed.filter (fun x => decide (16 ∉ x ∧ 18 ∉ x)) else d.allowed)

private theorem withoutSoutheastG_checked :
    feasible withoutSoutheastG ∅ = false := by decide +kernel

/-- The southeast owner may contain either or both G points.  No exact
one-point G budget is substituted for its original certified domain. -/
theorem southeast_g_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owner p 512).Inside (113/50) 2 ∨ (owner p 512).Inside 3 (8/5) := by
  classical
  have cover : 16 ∈ natCombinedOwners p (ownerIndex p 512) ∨
      18 ∈ natCombinedOwners p (ownerIndex p 512) := by
    by_contra absent
    push_neg at absent
    let actual := fun d : CertifiedDomain family =>
      natCombinedOwners p (ownerIndex p d.mask)
    have code : ∀ d ∈ domains, markerCode p (ownerIndex p d.mask) = d.mask := by
      intro d hd
      apply ownerIndex_spec
      rw [hf]
      exact domains_members d hd
    have allowed : List.Forall₂ (fun x d => x ∈ d)
        (domains.map actual) withoutSoutheastG := by
      rw [withoutSoutheastG,List.forall₂_map_left_iff,
        List.forall₂_map_right_iff,List.forall₂_same]
      intro d hd
      split_ifs with same
      · apply List.mem_filter.mpr
        refine ⟨d.sound p _ hf (code d hd),decide_eq_true ?_⟩
        simpa only [actual,same] using absent
      · exact d.sound p _ hf (code d hd)
    have disjoint : (domains.map actual).Pairwise Disjoint := by
      rw [List.pairwise_map]
      apply (List.Pairwise.and_mem.mp domains_distinct).imp
      intro a b h
      apply nat_combined_disjoint
      intro equal
      exact h.2.2 ((code a h.1).symm.trans
        ((congrArg (markerCode p) equal).trans (code b h.2.1)))
    exact rejected_domain_impossible _ withoutSoutheastG_checked
      (actual_owners_give_assignment _ _ ∅ allowed
        (by intros; exact Finset.disjoint_empty_right _) disjoint)
  rcases cover with own | own
  · left
    have point := (nat_combined_exact p (ownerIndex p 512) 16
      (by decide +kernel)).mpr own
    simpa [owner,auxPoints,fPoints,gPoints] using point
  · right
    have point := (nat_combined_exact p (ownerIndex p 512) 18
      (by decide +kernel)).mpr own
    simpa [owner,auxPoints,fPoints,gPoints] using point

#print axioms southeast_g_cover
end
end N12Compact.C868

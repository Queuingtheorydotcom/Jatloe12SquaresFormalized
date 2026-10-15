import Compact.Completion.CommonCases.OriginalOwners
import S12.DomainSpecData

/-! Small authentic ownership cuts for C702. Only the four ordinary
owner lists are needed; the merged owners are handled by actual nonempty
budgets and their genuine foreign points, outside any finite DFS. -/
namespace N12Compact.CommonCases.C702
open S12 S12Pilot OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

def family : Finset Nat := {1,2,12,16,32,192,256,1536,6144,8192,16384,32768}
private theorem budget_counts : (family∩auxExempt 0).card=3 ∧
    (family∩auxExempt 1).card=2 := by decide +kernel
private def direct (w : CombinedSpec) (hw : w.Check)
    (first : Bounds family w.mask w.first.val 0) (second : Bounds family w.mask w.second.val 1)
    (fNon : w.mask∉auxExempt 0) (gNon : w.mask∉auxExempt 1) : CertifiedDomain family :=
  restrict_budget23 family (ofCombined family w hw first second)
    budget_counts.1 budget_counts.2 fNon gNon
private def southAllowed : List (Finset Nat) := [{0,10},{0,12},{0,13},{2,10},{2,12},{2,13},{4,10},{4,12},{4,13},{0,1,13},{0,2,10},{0,2,12},{0,2,13},{0,4,10},{0,4,12},{0,4,13},{0,5,13},{1,4,13},{2,4,10},{2,4,12},{2,4,13},{4,5,13}]
private def southDomain : CertifiedDomain family :=
  cached_domain family
    (direct combinedSpec6 combinedSpec6_checked
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    256 southAllowed rfl rfl
private def bottomAllowed : List (Finset Nat) := [{2,12},{6,15},{2,4,12},{4,6,15}]
private def bottomDomain : CertifiedDomain family :=
  cached_domain family
    (direct combinedSpec19 combinedSpec19_checked
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    8192 bottomAllowed rfl rfl
private def rightAllowed : List (Finset Nat) := [{8,18},{9,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19}]
private def rightDomain : CertifiedDomain family :=
  cached_domain family
    (direct combinedSpec21 combinedSpec21_checked
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    16384 rightAllowed rfl rfl
private def topAllowed : List (Finset Nat) := [{3,14},{7,17},{3,5,14},{5,7,17}]
private def topDomain : CertifiedDomain family :=
  cached_domain family
    (direct combinedSpec24 combinedSpec24_checked
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    32768 topAllowed rfl rfl
private theorem south_checked : ∀ a∈southAllowed,
    Disjoint a ({0,10} : Finset Nat) → Disjoint a ({2,12} : Finset Nat) → ({4,13} : Finset Nat)⊆a := by
  decide +kernel
private theorem bottom_checked : ∀ b∈bottomAllowed,
    Disjoint b ({2,12} : Finset Nat) → ({6,15} : Finset Nat)⊆b := by decide +kernel
private theorem right_checked : ∀ r∈rightAllowed,
    Disjoint r ({9,19} : Finset Nat) → Disjoint r ({6,15} : Finset Nat) → ({8,18} : Finset Nat)⊆r := by
  decide +kernel
private theorem top_checked : ∀ t∈topAllowed,
    Disjoint t ({7,17} : Finset Nat) → ({3,14} : Finset Nat)⊆t := by decide +kernel

theorem pair_from_points (p : NormalizedPacking) (mask a b : Nat) (aBound : a<20) (bBound : b<20)
    (first : (owner p mask).Inside ((auxPoints 2)[a]!).1 ((auxPoints 2)[a]!).2)
    (second : (owner p mask).Inside ((auxPoints 2)[b]!).1 ((auxPoints 2)[b]!).2) :
    ({a,b} : Finset Nat)⊆auxiliaries p mask := by
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with ha | hb
  · rw [ha]
    exact (auxiliary_exact p mask a aBound).mp first
  · rw [hb]
    exact (auxiliary_exact p mask b bBound).mp second

theorem base_pairs (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (o : ({2,12} : Finset Nat)⊆auxiliaries p 1)
    (v : ({0,10} : Finset Nat)⊆auxiliaries p 2)
    (tr : ({7,17} : Finset Nat)⊆auxiliaries p 16)
    (nr : ({9,19} : Finset Nat)⊆auxiliaries p 32) :
    ({4,13} : Finset Nat)⊆auxiliaries p 256 ∧
      ({6,15} : Finset Nat)⊆auxiliaries p 8192 ∧
      ({8,18} : Finset Nat)⊆auxiliaries p 16384 ∧
      ({3,14} : Finset Nat)⊆auxiliaries p 32768 := by
  have aV := auxiliary_disjoint family p hf 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have aO := auxiliary_disjoint family p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have bO := auxiliary_disjoint family p hf 8192 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have b := bottom_checked _ (domain family bottomDomain p hf (by decide +kernel)) (bO.mono_right o)
  have rNR := auxiliary_disjoint family p hf 16384 32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have rB := auxiliary_disjoint family p hf 16384 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have tTR := auxiliary_disjoint family p hf 32768 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨south_checked _ (domain family southDomain p hf (by decide +kernel))
      (aV.mono_right v) (aO.mono_right o),b,
    right_checked _ (domain family rightDomain p hf (by decide +kernel))
      (rNR.mono_right nr) (rB.mono_right b),
    top_checked _ (domain family topDomain p hf (by decide +kernel)) (tTR.mono_right tr)⟩

theorem some_auxiliary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (kind : Fin 2) (ordinary : mask∉auxExempt kind) :
    ∃ j : Fin 10, (owner p mask).Inside ((auxPoints (auxKind kind))[j.val]!).1
      ((auxPoints (auxKind kind))[j.val]!).2 := by
  have hb := nat_aux_budget p kind (ownerIndex p mask)
  rw [code family p hf mask member] at hb
  simp only [ordinary,if_false] at hb
  have positive : 0 < (natAuxOwners p kind (ownerIndex p mask)).card := lt_of_lt_of_le (by decide) hb.1
  obtain ⟨j,hj⟩ := Finset.card_pos.mp positive
  have bound := Finset.mem_range.mp (nat_aux_subset p kind (ownerIndex p mask) hj)
  refine ⟨⟨j,bound⟩,?_⟩
  exact (nat_aux_exact p kind (ownerIndex p mask) j
    (by simpa only [aux_kind_length] using List.mem_range.mpr bound)).mpr hj

end
end N12Compact.CommonCases.C702

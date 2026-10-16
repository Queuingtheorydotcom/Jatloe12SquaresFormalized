import S12.DirectSingleDomain
import Compact.Bridge.RelaxedOwnerDomain

/-! Reuse a direct single-cover certificate on a contained cardinality
interval. Only the geometric third field of Check is used: the certificate's
original family need not be the actual family. Coordinate transport retains
the entire owned set and its cardinality, including extra ownership.
Source-only addition; no vendor declaration or certificate is changed. -/
namespace N12Compact.CommonCases.DirectSingleBudget
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem sound_of_budget (w : DirectSingleDomain) (hostFamily : Finset Nat) (k : Fin 2)
    (checked : w.Check hostFamily k) (q : OpenSquare)
    (side : 1<q.side) (size : q.side≤1001/1000) (box : InsideContainer q)
    (markers : ExactMarkers q (maskSupport w.mask)) (owned : Finset Nat)
    (actual : AuxExact q (auxKind k) owned) (subset : owned⊆Finset.range 10)
    (low : w.lower≤owned.card) (high : owned.card≤w.upper) : owned∈w.allowed := by
  rcases checked.2.2 owned (allAuxSubsets_complete owned subset) low high with allowed | rejected
  · exact allowed
  · obtain ⟨query,_,mask,kind,points⟩ := rejected
    exact False.elim (query.val.sound query.property q side size box
      (by simpa only [mask] using markers)
      (by simpa only [kind,points] using actual))

theorem actual_of_budget (w : DirectSingleDomain) (hostFamily : Finset Nat) (k : Fin 2)
    (checked : w.Check hostFamily k) (p : NormalizedPacking) (i : Fin 12)
    (mask : markerCode p i=w.mask)
    (low : w.lower≤(natAuxOwners p k i).card)
    (high : (natAuxOwners p k i).card≤w.upper) : natAuxOwners p k i∈w.allowed :=
  sound_of_budget w hostFamily k checked (p.square i)
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained i)
    (by simpa only [mask] using coded_exact p i) _ (nat_aux_exact p k i)
    (nat_aux_subset p k i) low high

/-- The actual family budget may have different endpoints. Containment
in the checked interval is sufficient; equality of upper bounds is not. -/
theorem actual_of_interval (w : DirectSingleDomain) (hostFamily actualFamily : Finset Nat)
    (k : Fin 2) (checked : w.Check hostFamily k) (p : NormalizedPacking) (i : Fin 12)
    (family : codedMarkerFamily p=actualFamily) (mask : markerCode p i=w.mask)
    (low : w.lower≤if w.mask∈auxExempt k then 0 else 1)
    (high : (actualFamily∩auxExempt k).card-2+
      (if w.mask∈auxExempt k then 0 else 1)≤w.upper) : natAuxOwners p k i∈w.allowed := by
  have bounds := nat_aux_budget p k i
  rw [family,mask] at bounds
  exact actual_of_budget w hostFamily k checked p i mask
    (low.trans bounds.1) (bounds.2.trans high)

private theorem mem_values (owned : Finset (Fin 10)) (j : Fin 10) :
    j.val∈owned.image Fin.val ↔ j∈owned := by
  constructor
  · intro h
    obtain ⟨k,hk,equal⟩ := Finset.mem_image.mp h
    exact (Fin.val_injective equal) ▸ hk
  · intro h
    exact Finset.mem_image.mpr ⟨j,h,rfl⟩

/-- The old and new auxiliary kinds may differ: a coordinate swap sends
the whole G list to a permutation of F, preserving every ownership bit. -/
theorem pull_exact (t : Transform) (q : OpenSquare) (sourceKind actualKind : Fin 2)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10,t.applyRat ((auxPoints (auxKind sourceKind))[j.val]!)=
      (auxPoints (auxKind actualKind))[(perm j).val]!)
    (owned : Finset (Fin 10))
    (actual : AuxExact q (auxKind actualKind) (owned.image Fin.val)) :
    AuxExact (t.pull q) (auxKind sourceKind) (RelaxedOwnerDomain.pulledOwners perm owned) := by
  intro j hj
  have jlt : j<10 := by simpa only [aux_kind_length] using List.mem_range.mp hj
  let J : Fin 10 := ⟨j,jlt⟩
  rw [rat_inside_transform]
  have point := points J
  change t.applyRat ((auxPoints (auxKind sourceKind))[j]!)=
    (auxPoints (auxKind actualKind))[(perm J).val]! at point
  rw [point,actual (perm J).val
    (by simpa only [aux_kind_length] using List.mem_range.mpr (perm J).isLt)]
  change (perm J).val∈owned.image Fin.val ↔ J.val∈RelaxedOwnerDomain.pulledOwners perm owned
  rw [mem_values,RelaxedOwnerDomain.mem_pulled]

theorem transformed_actual (w : DirectSingleDomain) (hostFamily : Finset Nat)
    (sourceKind actualKind : Fin 2) (checked : w.Check hostFamily sourceKind)
    (t : Transform) (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10,t.applyRat ((auxPoints (auxKind sourceKind))[j.val]!)=
      (auxPoints (auxKind actualKind))[(perm j).val]!)
    (p : NormalizedPacking) (i : Fin 12)
    (markers : ExactMarkers (t.pull (p.square i)) (maskSupport w.mask))
    (low : w.lower≤(natAuxOwners p actualKind i).card)
    (high : (natAuxOwners p actualKind i).card≤w.upper) :
    RelaxedOwnerDomain.pulledOwners perm (sortedAuxOwners p actualKind i)∈w.allowed := by
  have card := (RelaxedOwnerDomain.pulled_card perm (sortedAuxOwners p actualKind i)).trans
    (nat_aux_card p actualKind i).symm
  exact sound_of_budget w hostFamily sourceKind checked (t.pull (p.square i))
    (by simpa only [pull_same_side,p.congruent] using p.side_gt_one)
    (by simpa only [pull_same_side,p.congruent] using p.side_le)
    (container_transform t _ (p.contained i)) markers _
    (pull_exact t _ sourceKind actualKind perm points _ (nat_aux_exact p actualKind i))
    (RelaxedOwnerDomain.pulled_subset perm _)
    (by simpa only [card] using low) (by simpa only [card] using high)

end
#print axioms sound_of_budget
#print axioms actual_of_interval
#print axioms transformed_actual
end N12Compact.CommonCases.DirectSingleBudget

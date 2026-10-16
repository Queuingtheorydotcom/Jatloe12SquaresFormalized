import Compact.Completion.FiniteCases.TransposeOwnerDomain
import S12.DirectSingleDomain

/-! A typed local-query domain can be reused as local geometry, without
asserting that the transformed square belongs to its source family. The
target cardinality bounds are supplied by the actual target packing. -/
namespace N12Compact.FiniteCases.DirectHalfTransport
open S12 S12Pilot RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

theorem local_sound (w : DirectSingleDomain) (oldFamily : Finset Nat) (k : Fin 2)
    (checked : w.Check oldFamily k) (q : OpenSquare)
    (side : 1<q.side) (cap : q.side≤1001/1000) (box : InsideContainer q)
    (markers : ExactMarkers q (maskSupport w.mask))
    (owned : Finset Nat) (exactAux : AuxExact q (auxKind k) owned)
    (subset : owned⊆Finset.range 10) (low : w.lower≤owned.card)
    (high : owned.card≤w.upper) : owned∈w.allowed := by
  rcases checked.2.2 owned (allAuxSubsets_complete owned subset) low high with h | excluded
  · exact h
  · obtain ⟨query,_,mask,kind,equal⟩ := excluded
    exact False.elim (query.val.sound query.property q side cap box
      (by simpa only [mask] using markers)
      (by simpa only [kind,equal] using exactAux))

def transported (family : Finset Nat) (mask : Nat)
    (w : DirectSingleDomain) (oldFamily : Finset Nat) (k l : Fin 2)
    (checked : w.Check oldFamily k)
    (t : Transform) (valid : t∈allTransforms)
    (sourceMask : w.mask∈candidateMasks) (targetMask : t.maskAction w.mask=mask)
    (perm : Fin 10≃Fin 10)
    (points : ∀ j : Fin 10, t.applyRat ((auxPoints (auxKind k))[j.val]!)=
      (auxPoints (auxKind l))[(perm j).val]!)
    (budget : w.lower≤lower mask l ∧ upper family mask l≤w.upper) :
    OwnerBudget.HalfDomain family mask l :=
  ⟨w.allowed.map (pushOwners perm),by
    intro p i hf hi
    let owned := pulledOwners perm (sortedAuxOwners p l i)
    have card : owned.card=(natAuxOwners p l i).card :=
      (pulled_card perm _).trans (nat_aux_card p l i).symm
    have actual := nat_aux_budget p l i
    rw [hf,hi] at actual
    change lower mask l≤(natAuxOwners p l i).card ∧
      (natAuxOwners p l i).card≤upper family mask l at actual
    have lo : w.lower≤owned.card := by rw [card]; exact budget.1.trans actual.1
    have high : owned.card≤w.upper := by rw [card]; exact actual.2.trans budget.2
    have markers := exact_markers_pull t valid (p.square i) w.mask sourceMask
      (by simpa only [targetMask,hi] using coded_exact p i)
    have exactAux := TransposeOwnerDomain.cross_kind_exact t (p.square i) k l perm points
      (sortedAuxOwners p l i) (nat_aux_exact p l i)
    have member := local_sound w oldFamily k checked (t.pull (p.square i))
      (by simpa only [pull_same_side,p.congruent] using p.side_gt_one)
      (by simpa only [pull_same_side,p.congruent] using p.side_le)
      (container_transform t _ (p.contained i)) markers owned exactAux
      (pulled_subset perm _) lo high
    have result : pushOwners perm owned ∈ w.allowed.map (pushOwners perm) :=
      List.mem_map.mpr ⟨owned,member,rfl⟩
    simpa only [owned,push_pulled,natAuxOwners] using result⟩

def quarterFG : Fin 10≃Fin 10 :=
  Equiv.ofBijective ![5,2,8,0,6,3,9,1,7,4] (by decide +kernel)

theorem quarterFG_points (j : Fin 10) :
    (⟨true,true,false⟩ : Transform).applyRat ((auxPoints (auxKind 0))[j.val]!)=
      (auxPoints (auxKind 1))[(quarterFG j).val]! := by
  fin_cases j <;> decide +kernel

#print axioms transported
end
end N12Compact.FiniteCases.DirectHalfTransport

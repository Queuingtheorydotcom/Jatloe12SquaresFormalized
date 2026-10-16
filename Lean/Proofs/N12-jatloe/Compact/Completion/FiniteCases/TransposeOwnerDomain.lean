import Compact.Bridge.RelaxedOwnerDomain
import S12.DomainSpecData

/-! Transport a checked half-domain between the actual F and G grids.
The coordinate transformation acts on the whole original square; complete
ownership sets and their authentic cardinalities are preserved. -/
namespace N12Compact.FiniteCases.TransposeOwnerDomain
open S12 S12Pilot RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

def swapFG : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![2,5,0,8,3,6,1,9,4,7] (by decide +kernel)

theorem swapFG_points (j : Fin 10) :
    (⟨true,false,false⟩ : Transform).applyRat ((auxPoints 0)[j.val]!) =
      (auxPoints 1)[(swapFG j).val]! := by
  fin_cases j <;> decide +kernel

private theorem mem_values (owned : Finset (Fin 10)) (j : Fin 10) :
    j.val ∈ owned.image Fin.val ↔ j ∈ owned := by
  constructor
  · intro h
    obtain ⟨i,hi,equal⟩ := Finset.mem_image.mp h
    exact (Fin.val_injective equal) ▸ hi
  · exact fun h => Finset.mem_image.mpr ⟨j,h,rfl⟩

theorem cross_kind_exact (t : Transform) (q : OpenSquare) (k l : Fin 2)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10, t.applyRat ((auxPoints (auxKind k))[j.val]!) =
      (auxPoints (auxKind l))[(perm j).val]!)
    (owned : Finset (Fin 10))
    (actual : AuxExact q (auxKind l) (owned.image Fin.val)) :
    AuxExact (t.pull q) (auxKind k) (pulledOwners perm owned) := by
  intro j hj
  have bound : j < 10 := by
    simpa only [aux_kind_length] using List.mem_range.mp hj
  let J : Fin 10 := ⟨j,bound⟩
  rw [rat_inside_transform]
  have point := points J
  change t.applyRat ((auxPoints (auxKind k))[j]!) =
    (auxPoints (auxKind l))[(perm J).val]! at point
  rw [point,actual (perm J).val
    (by simpa only [aux_kind_length] using List.mem_range.mpr (perm J).isLt)]
  change (perm J).val ∈ owned.image Fin.val ↔ J.val ∈ pulledOwners perm owned
  rw [mem_values,mem_pulled]

/-- A geometric specification on one grid gives a necessary domain on the
other grid, whenever its size range covers this original family's budget. -/
def transported (family : Finset Nat) (mask : Nat)
    (w : SingleSpec) (checked : w.Check)
    (t : Transform) (valid : t ∈ allTransforms)
    (sourceMask : w.mask ∈ candidateMasks)
    (targetMask : t.maskAction w.mask = mask)
    (k l : Fin 2) (kind : w.kind = auxKind k)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10, t.applyRat ((auxPoints (auxKind k))[j.val]!) =
      (auxPoints (auxKind l))[(perm j).val]!)
    (budget : Bounds family mask w l) : OwnerBudget.HalfDomain family mask l :=
  ⟨w.allowed.map (pushOwners perm),by
    intro p i hf hi
    let owned := pulledOwners perm (sortedAuxOwners p l i)
    have card : owned.card = (natAuxOwners p l i).card :=
      (pulled_card perm _).trans (nat_aux_card p l i).symm
    have bounds := actual_bounds family mask w l budget p i hf hi
    rw [← card] at bounds
    have exactMarkers := exact_markers_pull t valid (p.square i) w.mask sourceMask
      (by simpa only [targetMask,hi] using coded_exact p i)
    have exactAux := cross_kind_exact t (p.square i) k l perm points
      (sortedAuxOwners p l i) (nat_aux_exact p l i)
    have member := w.sound checked (t.pull (p.square i))
      (by simpa only [pull_same_side,p.congruent] using p.side_gt_one)
      (by simpa only [pull_same_side,p.congruent] using p.side_le)
      (container_transform t _ (p.contained i)) exactMarkers owned
      (by simpa only [kind] using exactAux)
      (pulled_subset perm _) bounds.1 bounds.2
    have pushed : pushOwners perm owned ∈ w.allowed.map (pushOwners perm) :=
      List.mem_map.mpr ⟨owned,member,rfl⟩
    simpa only [owned,push_pulled,natAuxOwners] using pushed⟩

#print axioms transported
end
end N12Compact.FiniteCases.TransposeOwnerDomain

import Compact.Completion.C981.OutwardRows

/-! The original row 55 enters the outward-anchor contradiction after
transposing all actual owners and their points together. Its northwest
central owner supplies the outward point and the inward omission; no
ordinary-center or sampled-orientation premise is introduced. -/
namespace N12Compact.C981CompletionOutwardTranspose

open S12 S12Pilot S12Completion.C981 C981CompletionOutwardRows
set_option Elab.async false

def transpose : Transform := ⟨true,false,false⟩
def roles : Fin 12 → Fin 12 := ![1,0,4,3,2,7,6,5,9,8,11,10]

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, transpose.applyRat P ∈
    queryInsidePoints (ownerMasks (roles i)) 2 (v[(roles i).val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, transpose.applyRat P ∈
    queryOutsidePoints (ownerMasks (roles i)) 2 (v[(roles i).val]!))

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  let q : Fin 12 → OpenSquare := fun i => transpose.pull (owners p (roles i))
  have aux (i : Fin 12) : AuxExact (owners p (roles i)) 2 (v[(roles i).val]!) := by
    have he := ownership_entry_at p v hv (roles i)
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks (roles i)))
  have inside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ insidePoints i) :
      (q i).Inside P.1 P.2 := by
    apply (rat_inside_transform transpose (owners p (roles i)) P).mpr
    exact query_inside_sound _ 2 _ _ (owners_side_gt p (roles i))
      (owners_side_le p (roles i)) (owners_contained p (roles i))
      (owners_markers p hf (roles i)) (aux i) _ (checked.1 i P member)
  have outside (i : Fin 12) (P : ℚ × ℚ) (member : P ∈ outsidePoints i) :
      ¬ (q i).Inside P.1 P.2 := by
    intro h
    exact query_outside_sound _ 2 _ _ (owners_markers p hf (roles i)) (aux i) _
      (checked.2 i P member) ((rat_inside_transform transpose _ P).mp h)
  have side (i : Fin 12) : 1 < (q i).side := by
    simpa only [q,pull_same_side] using owners_side_gt p (roles i)
  have box (i : Fin 12) : InsideContainer (q i) :=
    container_transform _ _ (owners_contained p (roles i))
  have injective : Function.Injective roles := by decide +kernel
  have apart (i j : Fin 12) (different : i ≠ j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro x y h
    exact owners_disjoint p hf (roles i) (roles j)
      (fun eq => different (injective eq)) _ _
      ⟨(inside_pull transpose _ _ _).mp h.1,(inside_pull transpose _ _ _).mp h.2⟩
  exact geometry q side box inside outside apart

theorem checked55 : Check (representativeVectors[55]!) := by decide +kernel

theorem representative55_excluded : ExcludesVector (representativeVectors[55]!) :=
  excludes _ checked55

#print axioms geometry
#print axioms excludes
#print axioms representative55_excluded
end N12Compact.C981CompletionOutwardTranspose

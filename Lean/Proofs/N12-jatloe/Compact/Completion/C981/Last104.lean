import Compact.Completion.C981.LastRows

/-! The original row104 has the common-cycle entrance after transposing
the whole packing. This adapter pulls every point, wall and actual owner
together; its ordinary center belongs to original owner 5. -/
namespace N12Compact.C981CompletionLast104

open S12 S12Pilot S12Completion.C981 C981CompletionLastRows
set_option Elab.async false

def transpose : Transform := ⟨true,false,false⟩
def roles : Fin 12 → Fin 12 := ![1,0,4,3,2,7,6,5,9,8,11,10]

def Check (v : List (Finset Nat)) : Prop :=
  (∀ i, ∀ P ∈ insidePoints i, transpose.applyRat P ∈
    queryInsidePoints (ownerMasks (roles i)) 2 (v[(roles i).val]!)) ∧
  (∀ i, ∀ P ∈ outsidePoints i, transpose.applyRat P ∈
    queryOutsidePoints (ownerMasks (roles i)) 2 (v[(roles i).val]!)) ∧
  C981DoubleWallElbows.PlacementCheck v 0

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

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
      (checked.2.1 i P member) ((rat_inside_transform transpose _ P).mp h)
  have side (i : Fin 12) : 1 < (q i).side := by
    simpa only [q,pull_same_side] using owners_side_gt p (roles i)
  have cap (i : Fin 12) : (q i).side ≤ 1001/1000 := by
    simpa only [q,pull_same_side] using owners_side_le p (roles i)
  have same (i j : Fin 12) : (q i).side=(q j).side := by
    simpa only [q,pull_same_side,owners] using
      (p.congruent (ownerIndex p (ownerMasks (roles i)))).trans
        (p.congruent (ownerIndex p (ownerMasks (roles j)))).symm
  have box (i : Fin 12) : InsideContainer (q i) :=
    container_transform _ _ (owners_contained p (roles i))
  have injective : Function.Injective roles := by decide +kernel
  have apart (i j : Fin 12) (different : i ≠ j) :
      ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro x y h
    exact owners_disjoint p hf (roles i) (roles j)
      (fun eq => different (injective eq)) _ _
      ⟨(inside_pull transpose _ _ _).mp h.1,(inside_pull transpose _ _ _).mp h.2⟩
  have center : (q 7).Inside 2 2 := by
    have original := C981DoubleWallElbows.center v 0 checked.2.2 p hf hv
    change (transpose.pull (owners p 5)).Inside 2 2
    apply (inside_pull transpose _ _ _).mpr
    convert original using 1 <;> norm_num [C981DoubleWallElbows.placements,
      transpose,Transform.apply]
  exact geometry q side cap same box inside outside center apart

theorem checked : Check (representativeVectors[104]!) := by decide +kernel

theorem representative104_excluded : ExcludesVector (representativeVectors[104]!) :=
  excludes _ checked

#print axioms representative104_excluded
end N12Compact.C981CompletionLast104

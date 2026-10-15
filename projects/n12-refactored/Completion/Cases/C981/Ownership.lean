import Completion.Cases.C981.RowIdentity
import Mathlib.Data.List.OfFn

namespace S12Completion.C981
open S12 S12Pilot

/-- Original case-981 marker order in the saved exact plan. -/
def ownerMasks : Fin 12 → Nat :=
  ![1, 2, 12, 48, 192, 512, 1024, 2048, 4096, 8192, 16384, 32768]

theorem ownerMasks_mem : ∀ i, ownerMasks i ∈ family := by decide
theorem ownerMasks_injective : Function.Injective ownerMasks := by decide

noncomputable def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  p.square (ownerIndex p (ownerMasks i))

noncomputable def ownershipVector (p : NormalizedPacking) : List (Finset Nat) :=
  List.ofFn (fun i : Fin 12 => natCombinedOwners p (ownerIndex p (ownerMasks i)))

theorem ownership_entries (p : NormalizedPacking) (v : Fin 12 → Finset Nat)
    (hv : ownershipVector p = List.ofFn v) :
    ∀ i, natCombinedOwners p (ownerIndex p (ownerMasks i)) = v i :=
  congrFun (List.ofFn_injective hv)

theorem ownership_entry_at (p : NormalizedPacking) (v : List (Finset Nat))
    (hv : ownershipVector p = v) (i : Fin 12) :
    natCombinedOwners p (ownerIndex p (ownerMasks i)) = v[i.val]! := by
  have h := congrArg (fun xs : List (Finset Nat) => xs[i.val]!) hv
  simpa only [ownershipVector, List.getElem!_eq_getElem?_getD,
    List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some] using h

theorem owners_side_gt (p : NormalizedPacking) (i : Fin 12) :
    1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

theorem owners_side_le (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side ≤ 1001/1000 := by
  change (p.square _).side ≤ 1001/1000
  rw [p.congruent]
  exact p.side_le

theorem owners_contained (p : NormalizedPacking) (i : Fin 12) :
    InsideContainer (owners p i) := p.contained _

theorem owners_markers (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) : ExactMarkers (owners p i) (maskSupport (ownerMasks i)) := by
  have he := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  simpa only [owners, he] using coded_exact p (ownerIndex p (ownerMasks i))

theorem owners_disjoint (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (hij : i ≠ j) :
    ∀ x y, ¬ ((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro he
  have hi := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  have hj := ownerIndex_spec p (ownerMasks j) (by rw [hf]; exact ownerMasks_mem j)
  exact hij (ownerMasks_injective (hi.symm.trans ((congrArg (markerCode p) he).trans hj)))

theorem owners_auxiliary (p : NormalizedPacking) (v : Fin 12 → Finset Nat)
    (hv : ownershipVector p = List.ofFn v) (i : Fin 12) :
    AuxExact (owners p i) 2 (v i) := by
  simpa only [owners, ownership_entries p v hv i] using
    nat_combined_exact p (ownerIndex p (ownerMasks i))

theorem owners_query_inside (p : NormalizedPacking) (v : Fin 12 → Finset Nat)
    (hf : codedMarkerFamily p = family) (hv : ownershipVector p = List.ofFn v)
    (i : Fin 12) : ∀ P ∈ queryInsidePoints (ownerMasks i) 2 (v i),
      (owners p i).Inside P.1 P.2 :=
  query_inside_sound _ _ _ _ (owners_side_gt p i) (owners_side_le p i)
    (owners_contained p i) (owners_markers p hf i) (owners_auxiliary p v hv i)

theorem owners_query_outside (p : NormalizedPacking) (v : Fin 12 → Finset Nat)
    (hf : codedMarkerFamily p = family) (hv : ownershipVector p = List.ofFn v)
    (i : Fin 12) : ∀ P ∈ queryOutsidePoints (ownerMasks i) 2 (v i),
      ¬ (owners p i).Inside P.1 P.2 :=
  query_outside_sound _ _ _ _ (owners_markers p hf i) (owners_auxiliary p v hv i)

end S12Completion.C981

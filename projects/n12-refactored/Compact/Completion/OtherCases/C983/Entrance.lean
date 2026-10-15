import Compact.Completion.OtherCases.C983.RefinedDomains3

/-! Every original C983 packing has its complete actual twenty-point
ownership set in the displayed certified component domains. The original
component lists are a checked superset, never an added packing premise. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

def domains : Fin 12 → CertifiedDomain family :=
  ![stage3Owner0.val,stage3Owner1.val,stage3Owner2.val,stage3Owner3.val,stage3Owner4.val,stage3Owner5.val,stage3Owner6.val,stage3Owner7.val,stage3Owner8.val,stage3Owner9.val,stage3Owner10.val,stage3Owner11.val]

def originalComponents : Fin 12 → List (Finset Nat) :=
  ![[{2,12}],
    [{0,10}],
    [∅,{18},{8,18}],
    [∅,{19},{7},{7,17},{7,19},{9,19},{7,9,19}],
    [∅,{3},{3,14}],
    [{4,16},{4,18},{4,16,18},{4,5,16},{4,5,16,18},{8,16},{8,18},{8,16,18},{4,8,16},{4,8,18},{4,8,16,18},{5,8,16},{5,8,16,18},{4,5,8,16},{4,5,8,16,18},{4,9,16},{4,5,9,16},{8,9,16},{8,9,16,18},{8,9,16,19},{4,8,9,16},{4,8,9,16,18},{5,8,9,16},{5,8,9,16,18}],
    [{5,16},{5,14,16},{5,17},{5,14,17},{5,16,17},{5,19},{5,16,19},{5,17,19},{3,5,14,17},{4,5,16},{4,5,14,16},{4,5,16,17},{4,5,16,19},{7,16},{7,17},{7,16,17},{7,19},{7,16,19},{7,17,19},{5,7,16},{5,7,17},{5,7,14,17},{5,7,16,17},{5,7,19},{5,7,16,19},{5,7,17,19},{3,5,7,14,17},{4,5,7,16},{4,5,7,16,17},{4,5,7,16,19},{5,8,16},{5,8,14,16},{5,8,16,17},{4,5,8,16},{4,5,8,14,16},{4,5,8,16,17},{5,7,8,16},{5,7,8,16,17},{9,16},{9,17},{9,16,17},{9,19},{9,16,19},{9,17,19},{4,9,16},{4,9,16,17},{4,9,16,19},{5,9,16},{5,9,14,16},{5,9,17},{5,9,14,17},{5,9,16,17},{5,9,19},{5,9,16,19},{5,9,17,19},{4,5,9,16},{4,5,9,14,16},{4,5,9,16,17},{4,5,9,16,19},{7,9,16},{7,9,17},{7,9,16,17},{7,9,19},{7,9,16,19},{7,9,17,19},{4,7,9,16},{4,7,9,16,17},{4,7,9,16,19},{5,7,9,16},{5,7,9,17},{5,7,9,14,17},{5,7,9,16,17},{5,7,9,19},{5,7,9,16,19},{5,7,9,17,19},{8,9,16},{8,9,16,17},{8,9,16,18},{8,9,16,19},{4,8,9,16},{4,8,9,16,17},{4,8,9,16,19},{5,8,9,16},{5,8,9,14,16},{5,8,9,16,17},{5,8,9,16,19},{7,8,9,16},{7,8,9,16,17},{7,8,9,16,19}],
    [{13},{13,14},{13,16},{3,13},{3,13,14},{4,13},{4,13,14},{4,13,16},{3,4,13},{3,4,13,14},{5,13},{5,13,14},{5,13,16},{5,13,17},{3,5,13},{3,5,13,14},{3,5,13,16},{4,5,13},{4,5,13,14},{4,5,13,16},{4,5,13,17}],
    [{1,11},{1,3,11}],
    [{6,15},{6,15,18},{4,6,15}],
    [{8,18},{8,16,18},{9,19},{9,16,19},{7,9,19},{8,9,18},{8,9,16,18},{8,9,19},{8,9,16,19},{8,9,18,19},{7,8,9,19},{7,8,9,18,19}],
    [{3,14},{3,14,17},{3,5,14},{3,5,14,17},{7,17},{7,14,17},{7,17,19},{3,7,14,17},{5,7,17},{5,7,14,17},{3,5,7,14,17}]]

def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  p.square (ownerIndex p (ownerCode i))

def actual (p : NormalizedPacking) (i : Fin 12) : Finset Nat :=
  natCombinedOwners p (ownerIndex p (ownerCode i))

theorem domain_mask (i : Fin 12) : (domains i).mask=ownerCode i := by
  fin_cases i <;> rfl

theorem components_original (i : Fin 12) :
    ∀ owned∈(domains i).allowed,owned∈originalComponents i := by
  fin_cases i <;> decide +kernel

theorem owner_code (p : NormalizedPacking) (hf : codedMarkerFamily p=family) (i : Fin 12) :
    markerCode p (ownerIndex p (ownerCode i))=ownerCode i := by
  apply ownerIndex_spec
  rw [hf]
  fin_cases i <;> decide +kernel

theorem actual_mem (p : NormalizedPacking) (hf : codedMarkerFamily p=family) (i : Fin 12) :
    actual p i∈(domains i).allowed :=
  (domains i).sound p _ hf ((owner_code p hf i).trans (domain_mask i).symm)

/-- The authentic C983 component entrance, independently certified from
the original packing and without assuming the recovered 941-vector table. -/
theorem original_actual_mem (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (i : Fin 12) : actual p i∈originalComponents i :=
  components_original i _ (actual_mem p hf i)

theorem owners_side (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  rw [owners,p.congruent]
  exact p.side_gt_one

theorem owners_cap (p : NormalizedPacking) (i : Fin 12) : (owners p i).side ≤ 1001/1000 := by
  rw [owners,p.congruent]
  exact p.side_le

theorem owners_same_side (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by rw [owners,p.congruent,p.congruent]

theorem owners_contained (p : NormalizedPacking) (i : Fin 12) : InsideContainer (owners p i) :=
  p.contained _

theorem owners_markers (p : NormalizedPacking) (hf : codedMarkerFamily p=family) (i : Fin 12) :
    ExactMarkers (owners p i) (maskSupport (ownerCode i)) := by
  simpa only [owners,owner_code p hf i] using coded_exact p (ownerIndex p (ownerCode i))

private theorem codes_injective : Function.Injective ownerCode := by decide +kernel

theorem owners_apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family) (i j : Fin 12)
    (different : i ≠ j) : ∀ x y,¬((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro same
  apply different
  apply codes_injective
  exact (owner_code p hf i).symm.trans
    ((congrArg (markerCode p) same).trans (owner_code p hf j))

theorem actual_disjoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i ≠ j) : Disjoint (actual p i) (actual p j) := by
  apply nat_combined_disjoint
  intro same
  apply different
  apply codes_injective
  exact (owner_code p hf i).symm.trans
    ((congrArg (markerCode p) same).trans (owner_code p hf j))

theorem auxiliary_inside (p : NormalizedPacking) (i : Fin 12) (j : Nat)
    (bound : j < 20) (member : j∈actual p i) :
    (owners p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 := by
  apply (nat_combined_exact p (ownerIndex p (ownerCode i)) j ?_).mpr member
  change j∈List.range 20
  exact List.mem_range.mpr bound

theorem seed_inside (p : NormalizedPacking) (hf : codedMarkerFamily p=family) (i : Fin 12)
    (point : ℚ × ℚ) (member : point∈seedPoints (maskSupport (ownerCode i))) :
    (owners p i).Inside point.1 point.2 :=
  seed_points_sound (owners p i) (owners_side p i) (owners_cap p i) (owners_contained p i)
    (maskSupport (ownerCode i)) (owners_markers p hf i) point member

end
#print axioms original_actual_mem
end N12Compact.Completion.OtherCases.C983


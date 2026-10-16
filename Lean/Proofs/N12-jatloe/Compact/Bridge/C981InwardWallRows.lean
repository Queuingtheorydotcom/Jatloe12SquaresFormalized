import Compact.Geometry.C981InwardWall
import Completion.Cases.C981.VectorData

/-! Original vectors 36 and 106 share one actual wall-owner obstruction.
The foreign singleton point is strictly owned by original owner 1. -/
namespace N12Compact.C981InwardWallRows

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

def Check (v : List (Finset Nat)) : Prop :=
  (∀ P ∈ ([(457/500,2),(1,12/5),(87/50,2)] : List (ℚ × ℚ)),
    P ∈ queryInsidePoints (ownerMasks 8) 2 (v[8]!)) ∧
  (∀ P ∈ ([(1,87/50),(33/20,47/20)] : List (ℚ × ℚ)),
    P ∈ queryOutsidePoints (ownerMasks 8) 2 (v[8]!)) ∧
  ((19/25,187/100) : ℚ × ℚ) ∈ queryInsidePoints (ownerMasks 1) 2 (v[1]!)

instance (v : List (Finset Nat)) : Decidable (Check v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro p hf hv
  have aux (i : Fin 12) : AuxExact (owners p i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ)
      (member : P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) :
      (owners p i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ member
  have outside (P : ℚ × ℚ)
      (member : P ∈ queryOutsidePoints (ownerMasks 8) 2 (v[8]!)) :
      ¬ (owners p 8).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf 8) (aux 8) _ member
  apply C981InwardWall.impossible (owners p 8) (owners_side_gt p 8)
  · simpa using inside 8 (457/500,2) (checked.1 _ (by norm_num))
  · simpa using inside 8 (1,12/5) (checked.1 _ (by norm_num))
  · simpa using inside 8 (87/50,2) (checked.1 _ (by norm_num))
  · simpa using outside (1,87/50) (checked.2.1 _ (by norm_num))
  · simpa using outside (33/20,47/20) (checked.2.1 _ (by norm_num))
  · intro point
    exact owners_disjoint p hf 8 1 (by decide) _ _
      ⟨point,by simpa using inside 1 (19/25,187/100) checked.2.2⟩

def coveredIds : List Nat := [36,106]

theorem checked : ∀ i ∈ coveredIds, Check (representativeVectors[i]!) :=
  by decide +kernel

theorem covered_excluded (i : Nat) (hi : i ∈ coveredIds) :
    ExcludesVector (representativeVectors[i]!) := excludes _ (checked i hi)

#print axioms covered_excluded
end N12Compact.C981InwardWallRows

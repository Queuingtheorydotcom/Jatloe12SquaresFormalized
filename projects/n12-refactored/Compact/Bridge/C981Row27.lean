import Compact.Geometry.C981Row27
import Completion.Cases.C981.VectorData

/-! The complete original C981 representative 27. All compulsory points
come from its original marker masks and exact auxiliary ownership vector. -/
namespace N12Compact.C981Row27

open S12 S12Pilot S12Completion.C981
set_option Elab.async false

theorem representative27_excluded :
    ExcludesVector (representativeVectors[27]!) := by
  intro p hf hv
  let v := representativeVectors[27]!
  have aux (i : Fin 12) : AuxExact (owners p i) 2 (v[i.val]!) := by
    have he := ownership_entry_at p v hv i
    simpa only [owners,he] using nat_combined_exact p (ownerIndex p (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ)
      (member : P ∈ queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) :
      (owners p i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt p i) (owners_side_le p i)
      (owners_contained p i) (owners_markers p hf i) (aux i) _ member
  have outside (i : Fin 12) (P : ℚ × ℚ)
      (member : P ∈ queryOutsidePoints (ownerMasks i) 2 (v[i.val]!)) :
      ¬ (owners p i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers p hf i) (aux i) _ member
  apply C981Row27Geometry.impossible (owners p 7) (owners p 8) (owners p 11)
    (owners_side_gt p 7) (owners_side_gt p 8) (owners_contained p 8)
  · simpa using inside 7 (33/20,47/20) (by decide +kernel)
  · simpa using inside 7 (87/50,2) (by decide +kernel)
  · simpa using inside 7 (8/5,3) (by decide +kernel)
  · simpa using inside 8 (457/500,2) (by decide +kernel)
  · simpa using inside 8 (1,12/5) (by decide +kernel)
  · simpa using outside 8 (1,87/50) (by decide +kernel)
  · simpa using inside 11 (2,113/50) (by decide +kernel)
  · simpa using inside 11 (87/50,3) (by decide +kernel)
  · simpa using inside 11 (12/5,3) (by decide +kernel)
  · exact owners_disjoint p hf 7 8 (by decide)
  · exact owners_disjoint p hf 7 11 (by decide)

#print axioms representative27_excluded
end N12Compact.C981Row27

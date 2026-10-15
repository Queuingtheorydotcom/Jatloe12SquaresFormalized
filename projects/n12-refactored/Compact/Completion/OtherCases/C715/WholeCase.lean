import Compact.Completion.OtherCases.C715.Entrance
import Compact.Completion.OtherCases.C715.FourPointEnding
import Compact.Geometry.C715Segment

/-! Whole original C715 exclusion. The entrance is derived from the actual
packing and its authentic auxiliary budgets. Both local endings use genuine
foreign owners, and the southeast paired-corner point comes from the original
strict corner seed theorem. No terminal catalogue is assumed exhaustive. -/
namespace N12Compact.Completion.OtherCases.C715
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

def owners (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  p.square (ownerIndex p (ownerCode i))

theorem owner_code (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    markerCode p (ownerIndex p (ownerCode i)) = ownerCode i := by
  apply ownerIndex_spec
  rw [hf]
  fin_cases i <;> decide +kernel

theorem owners_side (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  rw [owners,p.congruent]
  exact p.side_gt_one

theorem owners_markers (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    ExactMarkers (owners p i) (maskSupport (ownerCode i)) := by
  simpa only [owners,owner_code p hf i] using
    coded_exact p (ownerIndex p (ownerCode i))

theorem owners_apart (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i j : Fin 12)
    (different : ownerCode i ≠ ownerCode j) :
    ∀ x y, ¬ ((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro same
  apply different
  exact (owner_code p hf i).symm.trans
    ((congrArg (markerCode p) same).trans (owner_code p hf j))

theorem auxiliary_inside (p : NormalizedPacking) (i : Fin 12) (j : Nat)
    (bound : j < 20)
    (owned : j ∈ natCombinedOwners p (ownerIndex p (ownerCode i))) :
    (owners p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 := by
  apply (nat_combined_exact p (ownerIndex p (ownerCode i)) j ?_).mpr owned
  change j ∈ List.range 20
  exact List.mem_range.mpr bound

theorem southeast_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : (owners p 2).Inside 3 1 := by
  have h := seed_points_sound (owners p 2) (owners_side p 2)
    (by rw [owners,p.congruent]; exact p.side_le)
    (p.contained _) (maskSupport 12) (owners_markers p hf 2) (3,1) (by decide +kernel)
  norm_num at h
  exact h

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  obtain ⟨hF5,hF6,hF9,branches⟩ := actual_cover p hf
  have f5 : (owners p 10).Inside 2 (113/50) := by
    have h := auxiliary_inside p 10 5 (by decide +kernel)
      (by simpa only [actual_entry p 10] using hF5)
    simpa [auxPoints,fPoints,gPoints] using h
  have f6 : (owners p 9).Inside (12/5) 1 := by
    have h := auxiliary_inside p 9 6 (by decide +kernel)
      (by simpa only [actual_entry p 9] using hF6)
    simpa [auxPoints,fPoints,gPoints] using h
  have f9 : (owners p 4).Inside 3 (113/50) := by
    have h := auxiliary_inside p 4 9 (by decide +kernel)
      (by simpa only [actual_entry p 4] using hF9)
    simpa [auxPoints,fPoints,gPoints] using h
  rcases branches with first | second
  · have g6 : (owners p 6).Inside (113/50) 2 := by
      have h := auxiliary_inside p 6 16 (by decide +kernel)
        (by simpa only [actual_entry p 6] using first.1)
      simpa [auxPoints,fPoints,gPoints] using h
    have g8 : (owners p 10).Inside 3 (8/5) := by
      have h := auxiliary_inside p 10 18 (by decide +kernel)
        (by simpa only [actual_entry p 10] using first.2)
      simpa [auxPoints,fPoints,gPoints] using h
    rcases four_point_ending (owners p 10) (owners_side p 10) f5 g8 with h | h
    · exact owners_apart p hf 10 6 (by decide +kernel) _ _ ⟨h,g6⟩
    · exact owners_apart p hf 10 4 (by decide +kernel) _ _ ⟨h,f9⟩
  · have g6 : (owners p 10).Inside (113/50) 2 := by
      have h := auxiliary_inside p 10 16 (by decide +kernel)
        (by simpa only [actual_entry p 10] using second.1)
      simpa [auxPoints,fPoints,gPoints] using h
    have g8 : (owners p 6).Inside 3 (8/5) := by
      have h := auxiliary_inside p 6 18 (by decide +kernel)
        (by simpa only [actual_entry p 6] using second.2)
      simpa [auxPoints,fPoints,gPoints] using h
    have markerSE : (owners p 6).Inside (47/20) (33/20) := by
      have h : Owns (owners p 6) 9 := (owners_markers p hf 6 9).mpr (by decide +kernel)
      simpa [Owns,marker] using h
    have right : (owners p 10).Inside (1543/500) 2 := by
      have h : Owns (owners p 10) 14 := (owners_markers p hf 10 14).mpr (by decide +kernel)
      simpa [Owns,marker] using h
    apply N12Compact.C715Segment.lower_points_foreign_square
      (owners p 6) (owners p 10) (owners_side p 6) markerSE g8
    · intro h
      exact owners_apart p hf 6 9 (by decide +kernel) _ _ ⟨h,f6⟩
    · intro h
      exact owners_apart p hf 6 2 (by decide +kernel) _ _ ⟨h,southeast_corner p hf⟩
    · exact g6
    · exact right
    · exact owners_apart p hf 6 10 (by decide +kernel)

/-- The unchanged historical-row and arbitrary-real-packing contract. -/
theorem whole_case : ExcludesCase 715 := excludes_case family_excluded

#print axioms whole_case
end
end N12Compact.Completion.OtherCases.C715

import Compact.Completion.OtherCases.C705716.Entrance
import Compact.Completion.OtherCases.ThreeCentral.TwoSquares

/-! Complete original-case source proofs of C705 and C716. The ownership
labels are derived from the authentic family budgets; the geometry compares
the two complete actual central squares. Reflection moves every point and
owner together and retains the common physical side and strict disjointness. -/
namespace N12Compact.Completion.OtherCases.C705716
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

def owners (b : Bool) (p : NormalizedPacking) (i : Fin 12) : OpenSquare :=
  p.square (ownerIndex p (ownerCode b i))

theorem owner_code (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 12) :
    markerCode p (ownerIndex p (ownerCode b i)) = ownerCode b i := by
  apply ownerIndex_spec
  rw [hf]
  cases b <;> fin_cases i <;> decide +kernel

theorem owners_side (b : Bool) (p : NormalizedPacking) (i : Fin 12) :
    1 < (owners b p i).side := by
  rw [owners,p.congruent]
  exact p.side_gt_one

theorem owners_same (b : Bool) (p : NormalizedPacking) (i j : Fin 12) :
    (owners b p i).side = (owners b p j).side := by
  simp only [owners,p.congruent]

theorem owners_markers (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 12) :
    ExactMarkers (owners b p i) (maskSupport (ownerCode b i)) := by
  simpa only [owners,owner_code b p hf i] using
    coded_exact p (ownerIndex p (ownerCode b i))

theorem owners_apart (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i j : Fin 12)
    (different : ownerCode b i ≠ ownerCode b j) :
    ∀ x y, ¬ ((owners b p i).Inside x y ∧ (owners b p j).Inside x y) := by
  apply p.disjoint
  intro same
  apply different
  exact (owner_code b p hf i).symm.trans
    ((congrArg (markerCode p) same).trans (owner_code b p hf j))

theorem auxiliary_inside (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 12) (j : Nat)
    (bound : j < 20) (owned : j ∈ (expectedVector b)[i.val]!) :
    (owners b p i).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 := by
  have actual : j ∈ natCombinedOwners p (ownerIndex p (ownerCode b i)) := by
    rw [← actual_entry b p i,actual_cover b p hf]
    exact owned
  apply (nat_combined_exact p (ownerIndex p (ownerCode b i)) j ?_).mpr actual
  change j ∈ List.range 20
  exact List.mem_range.mpr bound

theorem marker_inside (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 12) (j : Marker)
    (owned : j ∈ maskSupport (ownerCode b i)) :
    (owners b p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers b p hf i j).mpr owned

theorem family705_excluded : ExcludesFamily (family false) := by
  intro p hf
  have sw : (owners false p 6).Inside (33/20) (33/20) := by
    simpa [marker] using marker_inside false p hf 6 8 (by decide +kernel)
  have d : (owners false p 6).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside false p hf 6 4 (by decide +kernel) (by decide +kernel)
  have q : (owners false p 6).Inside (87/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside false p hf 6 13 (by decide +kernel) (by decide +kernel)
  have bottom : (owners false p 0).Inside (8/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside false p hf 0 2 (by decide +kernel) (by decide +kernel)
  have left : (owners false p 1).Inside 1 (8/5) := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside false p hf 1 10 (by decide +kernel) (by decide +kernel)
  apply N12Compact.Completion.OtherCases.ThreeCentral.impossible
    (owners false p 6) (owners false p 7) (owners_side false p 6)
    (owners_same false p 6 7) sw d q
  · intro h
    exact owners_apart false p hf 6 0 (by decide +kernel) _ _ ⟨h,bottom⟩
  · intro h
    exact owners_apart false p hf 6 1 (by decide +kernel) _ _ ⟨h,left⟩
  · simpa [marker] using marker_inside false p hf 7 9 (by decide +kernel)
  · simpa [marker] using marker_inside false p hf 7 10 (by decide +kernel)
  · simpa [marker] using marker_inside false p hf 7 11 (by decide +kernel)
  · exact owners_apart false p hf 6 7 (by decide +kernel)

theorem family716_excluded : ExcludesFamily (family true) := by
  intro p hf
  let A := pullX (owners true p 6)
  let H := pullX (owners true p 7)
  have equivalentA (x y : ℝ) : A.Inside x y ↔ (owners true p 6).Inside (4-x) y :=
    inside_pullX _ _ _
  have equivalentH (x y : ℝ) : H.Inside x y ↔ (owners true p 7).Inside (4-x) y :=
    inside_pullX _ _ _
  have se : (owners true p 6).Inside (47/20) (33/20) := by
    simpa [marker] using marker_inside true p hf 6 9 (by decide +kernel)
  have d : (owners true p 6).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside true p hf 6 4 (by decide +kernel) (by decide +kernel)
  have q : (owners true p 6).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside true p hf 6 16 (by decide +kernel) (by decide +kernel)
  have bottom : (owners true p 9).Inside (12/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside true p hf 9 6 (by decide +kernel) (by decide +kernel)
  have right : (owners true p 10).Inside 3 (8/5) := by
    simpa [auxPoints,fPoints,gPoints] using
      auxiliary_inside true p hf 10 18 (by decide +kernel) (by decide +kernel)
  apply N12Compact.Completion.OtherCases.ThreeCentral.impossible A H
    (by simpa [A,pullX] using owners_side true p 6)
    (by simpa [A,H,pullX] using owners_same true p 6 7)
  · apply (equivalentA _ _).mpr
    norm_num
    exact se
  · apply (equivalentA _ _).mpr
    norm_num
    exact d
  · apply (equivalentA _ _).mpr
    norm_num
    exact q
  · intro h
    have actual : (owners true p 6).Inside (12/5) 1 := by
      have h' := (equivalentA _ _).mp h
      norm_num at h'
      exact h'
    exact owners_apart true p hf 6 9 (by decide +kernel) _ _ ⟨actual,bottom⟩
  · intro h
    have actual : (owners true p 6).Inside 3 (8/5) := by
      have h' := (equivalentA _ _).mp h
      norm_num at h'
      exact h'
    exact owners_apart true p hf 6 10 (by decide +kernel) _ _ ⟨actual,right⟩
  · apply (equivalentH _ _).mpr
    norm_num
    simpa [marker] using marker_inside true p hf 7 8 (by decide +kernel)
  · apply (equivalentH _ _).mpr
    norm_num
    simpa [marker] using marker_inside true p hf 7 11 (by decide +kernel)
  · apply (equivalentH _ _).mpr
    norm_num
    simpa [marker] using marker_inside true p hf 7 10 (by decide +kernel)
  · intro x y h
    exact owners_apart true p hf 6 7 (by decide +kernel) (4-x) y
      ⟨(equivalentA _ _).mp h.1,(equivalentH _ _).mp h.2⟩

theorem case705_excluded : ExcludesCase 705 := excludes_case false family705_excluded
theorem case716_excluded : ExcludesCase 716 := excludes_case true family716_excluded

#print axioms case705_excluded
#print axioms case716_excluded
end
end N12Compact.Completion.OtherCases.C705716

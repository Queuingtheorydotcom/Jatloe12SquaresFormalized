import Compact.Geometry.WallCenterBarrier
import Completion.Cases.C977.AuxiliaryContext

/-! Case 977 loses twelve wall branches uniformly over all 57 actual auxiliary
vectors. The four remaining branches retain the original packing, canonical
missing corner, exact ownership vector, and both undecided opposite walls.
No whole vector or whole case is declared excluded by this module. -/
namespace N12Compact.C977WallCenters
open S12 S12Pilot S12Completion S12Completion.C977
set_option Elab.async false

private theorem left_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (p.square (orderedOwner p 8)).Inside 1 (12/5) ∧
      ¬ (p.square (orderedOwner p 8)).Inside (87/50) 2 := by
  have domain := pruned_auxiliary_domain_actual p hf 8
  have checks : ∀ owned ∈ pruningDomain4 8, 11 ∈ owned ∧ 13 ∉ owned := by decide
  have owned := checks _ domain
  constructor
  · have hp := (nat_combined_exact p (orderedOwner p 8) 11 (by decide)).mpr owned.1
    simpa [auxPoints, fPoints, gPoints] using hp
  · intro hp
    apply owned.2
    apply (nat_combined_exact p (orderedOwner p 8) 13 (by decide)).mp
    simpa [auxPoints, fPoints, gPoints] using hp

private theorem bottom_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (p.square (orderedOwner p 9)).Inside (12/5) 1 ∧
      ¬ (p.square (orderedOwner p 9)).Inside 2 (87/50) := by
  have domain := pruned_auxiliary_domain_actual p hf 9
  have checks : ∀ owned ∈ pruningDomain4 9, 6 ∈ owned ∧ 4 ∉ owned := by decide
  have owned := checks _ domain
  constructor
  · have hp := (nat_combined_exact p (orderedOwner p 9) 6 (by decide)).mpr owned.1
    simpa [auxPoints, fPoints, gPoints] using hp
  · intro hp
    apply owned.2
    apply (nat_combined_exact p (orderedOwner p 9) 4 (by decide)).mp
    simpa [auxPoints, fPoints, gPoints] using hp

/-- The left owner's actual center lies strictly above the wall split. -/
theorem left_center (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    2 < centerY (p.square (orderedOwner p 8)) := by
  have code := ordered_owner_code p hf 8
  have exactMarkers := coded_exact p (orderedOwner p 8)
  rw [code] at exactMarkers
  have hP : (p.square (orderedOwner p 8)).Inside (457/500) 2 := by
    have hp := (exactMarkers 12).mpr (by decide)
    simpa [Owns, marker] using hp
  have anchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have apart : orderedOwner p 8 ≠ orderedOwner p 1 := by
    intro h
    exact (by decide : (8 : Fin 12) ≠ 1) (ordered_owner_injective p hf h)
  have hW : ¬ (p.square (orderedOwner p 8)).Inside (19/25) (187/100) :=
    fun hp => p.disjoint _ _ apart _ _ ⟨hp,anchors.2.2⟩
  have aux := left_auxiliary p hf
  exact WallCenterBarrier.center_above _
    (by rw [p.congruent]; exact p.side_gt_one) (p.contained _) hP aux.1 hW aux.2

/-- Coordinate transposition gives the bottom owner's strict rightward cut. -/
theorem bottom_center (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    2 < centerX (p.square (orderedOwner p 9)) := by
  have code := ordered_owner_code p hf 9
  have exactMarkers := coded_exact p (orderedOwner p 9)
  rw [code] at exactMarkers
  have hP : (p.square (orderedOwner p 9)).Inside 2 (457/500) := by
    have hp := (exactMarkers 13).mpr (by decide)
    simpa [Owns, marker] using hp
  have anchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have apart : orderedOwner p 9 ≠ orderedOwner p 0 := by
    intro h
    exact (by decide : (9 : Fin 12) ≠ 0) (ordered_owner_injective p hf h)
  have hW : ¬ (p.square (orderedOwner p 9)).Inside (187/100) (19/25) :=
    fun hp => p.disjoint _ _ apart _ _ ⟨hp,anchors.lower_point⟩
  have aux := bottom_auxiliary p hf
  have high := WallCenterBarrier.center_above (pullSwap (p.square (orderedOwner p 9)))
    (by change 1 < (p.square (orderedOwner p 9)).side; rw [p.congruent]; exact p.side_gt_one)
    (container_pullSwap _ (p.contained _))
    ((inside_pullSwap _ _ _).mpr hP) ((inside_pullSwap _ _ _).mpr aux.1)
    (fun hp => hW ((inside_pullSwap _ _ _).mp hp))
    (fun hp => aux.2 ((inside_pullSwap _ _ _).mp hp))
  simpa only [center_pullSwap_y] using high

/-- Both lower-half choices are impossible, uniformly in the complete vector.
Only the right and top owners still require wall branches. -/
theorem wall_branch_restriction (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (w : WallOwners p) (b : WallBranch)
    (hb : WallHalfSpaces p w b) : b 0 = false ∧ b 1 = false := by
  have hi0 : w.index 0 = orderedOwner p 8 := by
    apply markerCode_injective p
    rw [w.code, ordered_owner_code p hf]
    rfl
  have hi1 : w.index 1 = orderedOwner p 9 := by
    apply markerCode_injective p
    rw [w.code, ordered_owner_code p hf]
    rfl
  constructor
  · cases h : b 0 with
    | false => rfl
    | true =>
      have low := hb 0
      rw [h] at low
      change centerY (p.square (w.index 0)) ≤ 2 at low
      rw [hi0] at low
      exact False.elim ((not_le_of_gt (left_center p hf)) low)
  · cases h : b 1 with
    | false => rfl
    | true =>
      have low := hb 1
      rw [h] at low
      change centerX (p.square (w.index 1)) ≤ 2 at low
      rw [hi1] at low
      exact False.elim ((not_le_of_gt (bottom_center p hf)) low)

abbrev OppositeWallBranch := Bool × Bool

def expandWallBranch (b : OppositeWallBranch) : WallBranch :=
  ![false, false, b.1, b.2]

private theorem expand_of_restriction (b : WallBranch)
    (h : b 0 = false ∧ b 1 = false) : expandWallBranch (b 2, b 3) = b := by
  funext k
  fin_cases k <;> simp [expandWallBranch, h.1, h.2]

abbrev ReducedContextIndex := OppositeWallBranch × Fin auxiliaryVectors.length

theorem reduced_context_count : Fintype.card ReducedContextIndex = 228 := by
  norm_num [ReducedContextIndex, OppositeWallBranch, Fintype.card_prod,
    auxiliary_vector_count]

/-- Original coverage, now with four rather than sixteen wall branches.
All missing-corner and actual ownership premises are preserved verbatim. -/
theorem canonical_four_wall_context_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q, ∃ c : ReducedContextIndex,
        WallHalfSpaces q w (expandWallBranch c.1) ∧
        auxiliaryVectors.get c.2 = actualAuxiliaryVector q := by
  obtain ⟨q,hframe,hq,hm,hbounds,w,c,hb,hv⟩ := canonical_auxiliary_context_cover p hf
  have he := expand_of_restriction c.1 (wall_branch_restriction q hq w c.1 hb)
  refine ⟨q,hframe,hq,hm,hbounds,w,((c.1 2,c.1 3),c.2),?_,hv⟩
  change WallHalfSpaces q w (expandWallBranch (c.1 2,c.1 3))
  rw [he]
  exact hb

/-- Honest remaining interface: every one of the 57 vectors still requires
exclusion in each of the four surviving wall branches. -/
theorem excludes_case_of_four_wall_contexts
    (hcontext : ∀ (p : NormalizedPacking),
      codedMarkerFamily p = family →
      StrengthenedMissingCorner (p.square (orderedOwner p 0)) →
      CanonicalCornerBounds (p.square (orderedOwner p 0)) →
      ∀ (w : WallOwners p) (c : ReducedContextIndex),
        WallHalfSpaces p w (expandWallBranch c.1) →
        auxiliaryVectors.get c.2 = actualAuxiliaryVector p → False) : ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨q,_,hq,hm,hbounds,w,c,hb,hv⟩ := canonical_four_wall_context_cover p hf
  exact hcontext q hq hm hbounds w c hb hv

#print axioms wall_branch_restriction
#print axioms excludes_case_of_four_wall_contexts
end N12Compact.C977WallCenters

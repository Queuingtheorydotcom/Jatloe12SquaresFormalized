import Completion.Cases.C977.Context
import Completion.Cases.C977.AuxiliaryVectors

namespace S12Completion.C977
open S12

/-- The entire closed wall-direction and complete auxiliary-vector universe.
    Contexts can overlap at a wall split; every vector is distinct. -/
abbrev ContextIndex := WallBranch × Fin auxiliaryVectors.length

theorem context_count : Fintype.card ContextIndex = 912 := by
  rw [Fintype.card_prod, wall_branch_count, Fintype.card_fin, auxiliary_vector_count]

/-- The canonical missing-corner owner is slot zero in the proved owner
    order, not an assumed original square label. -/
theorem ordered_missing_corner_owner (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12)
    (hi : markerCode p i = 1) : orderedOwner p 0 = i := by
  apply markerCode_injective p
  have ho := ordered_owner_code p hf 0
  change markerCode p (orderedOwner p 0) = 1 at ho
  exact ho.trans hi.symm

/-- Every actual packing enters one of the 912 contexts in one common
    canonical frame, with its entire actual ownership vector and the
    strengthened missing corner at ordered slot zero. No context is
    excluded by this coverage theorem. -/
theorem canonical_auxiliary_context_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q, ∃ c : ContextIndex,
        WallHalfSpaces q w c.1 ∧
        auxiliaryVectors.get c.2 = actualAuxiliaryVector q := by
  obtain ⟨q, hframe, hq, i, j, hi, hj, hij, hm, hbounds, w, b, hb⟩ :=
    canonical_bounded_wall_context_cover p hf
  have ho := ordered_missing_corner_owner q hq i hi
  obtain ⟨v, hv⟩ := List.mem_iff_get.mp (actual_auxiliary_vector_mem q hq)
  refine ⟨q, hframe, hq, ?_, ?_, w, (b, v), hb, hv⟩
  · simpa only [ho] using hm
  · simpa only [ho] using hbounds

theorem retained_canonical_auxiliary_context_cover
    (r : CoverRow) (hr : r ∈ retainedRows) (hid : r.originalId = 977)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = r.groups) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      StrengthenedMissingCorner (q.square (orderedOwner q 0)) ∧
      CanonicalCornerBounds (q.square (orderedOwner q 0)) ∧
      ∃ w : WallOwners q, ∃ c : ContextIndex,
        WallHalfSpaces q w c.1 ∧
        auxiliaryVectors.get c.2 = actualAuxiliaryVector q :=
  canonical_auxiliary_context_cover p (hf.trans (row_family r hr hid))

/-- Full case exclusion still needs universal geometric contradictions for
    every context in the single canonical root. The exact table size and
    exhaustive coverage do not supply those contradictions. -/
theorem excludes_case_of_auxiliary_contexts
    (hcontext : ∀ (p : NormalizedPacking),
      codedMarkerFamily p = family →
      StrengthenedMissingCorner (p.square (orderedOwner p 0)) →
      CanonicalCornerBounds (p.square (orderedOwner p 0)) →
      ∀ (w : WallOwners p) (c : ContextIndex),
        WallHalfSpaces p w c.1 →
        auxiliaryVectors.get c.2 = actualAuxiliaryVector p → False) :
    ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨q, _, hq, hm, hbounds, w, c, hb, hv⟩ :=
    canonical_auxiliary_context_cover p hf
  exact hcontext q hq hm hbounds w c hb hv

end S12Completion.C977

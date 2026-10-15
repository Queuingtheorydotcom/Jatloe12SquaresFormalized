import Completion.Cases.C977.SwapReduction
import Completion.Cases.C977.WallBranches
import Completion.Cases.C977.MissingCornerBounds
import Completion.Cases.C977.InteriorFaces
import Completion.Cases.C977.UnusedMarkerDistance

namespace S12Completion.C977
open S12

/-- Derive wall directions in the chosen canonical packing, after the whole
    packing has been transposed if needed. Every geometric hypothesis uses
    this one frame; no saved auxiliary context is implicitly transported. -/
theorem canonical_wall_context_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      ∃ i j : Fin 12,
        markerCode q i = 1 ∧ markerCode q j = 2 ∧ i ≠ j ∧
        StrengthenedMissingCorner (q.square i) ∧
        ∃ w : WallOwners q, ∃ b : WallBranch, WallHalfSpaces q w b := by
  obtain ⟨q, hframe, hq, i, j, hi, hj, hij, hmissing⟩ :=
    canonical_missing_corner_cover p hf
  obtain ⟨w, b, hb⟩ := case_wall_branch_cover q hq
  exact ⟨q, hframe, hq, i, j, hi, hj, hij, hmissing, w, b, hb⟩

/-- Coverage includes every retained row with original ID 977 and every
    actual normalized packing realizing that row, including all split ties. -/
theorem retained_canonical_wall_context_cover
    (r : CoverRow) (hr : r ∈ retainedRows) (hid : r.originalId = 977)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = r.groups) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      ∃ i j : Fin 12,
        markerCode q i = 1 ∧ markerCode q j = 2 ∧ i ≠ j ∧
        StrengthenedMissingCorner (q.square i) ∧
        ∃ w : WallOwners q, ∃ b : WallBranch, WallHalfSpaces q w b :=
  canonical_wall_context_cover p (hf.trans (row_family r hr hid))

/-- The chosen canonical corner has the exact normal-component gap as well
    as the strengthened strict points, before any wall branch is pruned. -/
theorem canonical_bounded_wall_context_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ codedMarkerFamily q = family ∧
      ∃ i j : Fin 12,
        markerCode q i = 1 ∧ markerCode q j = 2 ∧ i ≠ j ∧
        StrengthenedMissingCorner (q.square i) ∧
        CanonicalCornerBounds (q.square i) ∧
        ∃ w : WallOwners q, ∃ b : WallBranch, WallHalfSpaces q w b := by
  obtain ⟨q, hframe, hq, i, j, hi, hj, hij, hmissing, w, b, hb⟩ :=
    canonical_wall_context_cover p hf
  exact ⟨q, hframe, hq, i, j, hi, hj, hij, hmissing,
    code_one_missing_corner_bounds q i hi hmissing, w, b, hb⟩

/-- Refuting every closed wall branch of the single canonical root suffices
    for the complete case contract. The sixteen branch contradictions are
    still unsupplied; coverage alone is not a case exclusion. -/
theorem excludes_case_of_canonical_wall_contexts
    (hbranch : ∀ (p : NormalizedPacking) (i j : Fin 12),
      codedMarkerFamily p = family →
      markerCode p i = 1 → markerCode p j = 2 → i ≠ j →
      StrengthenedMissingCorner (p.square i) →
      ∀ (w : WallOwners p) (b : WallBranch), WallHalfSpaces p w b → False) :
    ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨q, _, hq, i, j, hi, hj, hij, hmissing, w, b, hb⟩ :=
    canonical_wall_context_cover p hf
  exact hbranch q i j hq hi hj hij hmissing w b hb

end S12Completion.C977

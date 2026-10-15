import Completion.Cases.C977.Anchors

namespace S12Completion.C977
open S12 S12Pilot
set_option maxHeartbeats 200000

/-- The established entrance and original anchors discharge the complete
    hypotheses of the missing-corner strengthening. -/
theorem missing_corner_points (q : OpenSquare) (h : MissingCornerEntrance q)
    (hanchors : SingletonAnchors q) : MissingCornerPoints q :=
  missing_corner_points_of_anchors q h.side_gt_one h.contained h.marker_owned
    hanchors h.corner_missing

theorem code_one_missing_points (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 1) (hz : ¬(p.square i).Inside 1 1) :
    MissingCornerPoints (p.square i) :=
  missing_corner_points _ (code_one_missing_entrance p i hi hz) (code_one_anchors p i hi)

theorem code_two_missing_points (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2) (hz : ¬(p.square i).Inside 1 1) :
    MissingCornerPoints (S12.pullSwap (p.square i)) :=
  missing_corner_points _ (code_two_missing_entrance p i hi hz) (code_two_anchors p i hi)

/-- Coordinate transport back to the original packing frame for code 2. -/
theorem code_two_original_missing_points (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2) (hz : ¬(p.square i).Inside 1 1) :
    (p.square i).Inside 1 (91 / 50) ∧
    (p.square i).Inside (19 / 25) (49 / 25) := by
  obtain ⟨h0, h1⟩ := code_two_missing_points p i hi hz
  simpa only [S12.inside_pullSwap] using And.intro h0 h1

/-- Each covered root retains its entrance and anchors and gains both
    additional strict points. This strengthens the roots without excluding
    either root or changing the original owner labels. -/
structure StrengthenedMissingCorner (q : OpenSquare) : Prop where
  entrance : MissingCornerEntrance q
  anchors : SingletonAnchors q
  points : MissingCornerPoints q

theorem missing_corner_strengthening_cover (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      (StrengthenedMissingCorner (p.square i) ∨
        ((p.square i).Inside 1 1 ∧
          StrengthenedMissingCorner (S12.pullSwap (p.square j)))) := by
  obtain ⟨i, j, hi, hj, hij, ha0, ha1, hroot⟩ :=
    anchored_missing_corner_entrance_cover p hf
  refine ⟨i, j, hi, hj, hij, ?_⟩
  rcases hroot with hroot | ⟨hpresent, hroot⟩
  · exact Or.inl ⟨hroot, ha0, missing_corner_points _ hroot ha0⟩
  · exact Or.inr ⟨hpresent, hroot, ha1, missing_corner_points _ hroot ha1⟩

theorem retained_missing_corner_strengthening_cover
    (r : S12.CoverRow) (hr : r ∈ S12.retainedRows) (hid : r.originalId = 977)
    (p : S12.NormalizedPacking) (hf : S12.codedMarkerFamily p = r.groups) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      (StrengthenedMissingCorner (p.square i) ∨
        ((p.square i).Inside 1 1 ∧
          StrengthenedMissingCorner (S12.pullSwap (p.square j)))) := by
  apply missing_corner_strengthening_cover p
  exact hf.trans (row_family r hr hid)

/-- Conditional assembly from contradictions in both complete strengthened
    roots. Every premise quantifies over the actual packing, whole marker
    family and original owner labels. Neither contradiction is supplied here. -/
theorem excludes_case_of_strengthened_corner_roots
    (hroot0 : ∀ (p : S12.NormalizedPacking) (i j : Fin 12),
      S12.codedMarkerFamily p = family →
      S12.markerCode p i = 1 → S12.markerCode p j = 2 → i ≠ j →
      StrengthenedMissingCorner (p.square i) → False)
    (hroot1 : ∀ (p : S12.NormalizedPacking) (i j : Fin 12),
      S12.codedMarkerFamily p = family →
      S12.markerCode p i = 1 → S12.markerCode p j = 2 → i ≠ j →
      (p.square i).Inside 1 1 →
      StrengthenedMissingCorner (S12.pullSwap (p.square j)) → False) :
    ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨i, j, hi, hj, hij, hroot⟩ := missing_corner_strengthening_cover p hf
  rcases hroot with hroot | ⟨hpresent, hroot⟩
  · exact hroot0 p i j hf hi hj hij hroot
  · exact hroot1 p i j hf hi hj hij hpresent hroot

end S12Completion.C977

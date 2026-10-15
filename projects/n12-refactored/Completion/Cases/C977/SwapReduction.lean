import Completion.Cases.C977.MissingCornerPoints

namespace S12Completion.C977

/-- Transpose the entire packing using Jatloe's original container symmetry. -/
def transpose : S12.Transform := ⟨true, false, false⟩

theorem transpose_mem : transpose ∈ S12.allTransforms := by decide

/-- Case 977 is fixed by transposition, including every marker owner. -/
theorem transpose_family_masks : family.image transpose.maskAction = family := by
  decide

theorem transpose_mask_involution :
    ∀ m ∈ family, transpose.maskAction (transpose.maskAction m) = m := by
  decide

noncomputable def transposePacking (p : S12.NormalizedPacking) : S12.NormalizedPacking :=
  transpose.pullPacking p

theorem transpose_square (p : S12.NormalizedPacking) (i : Fin 12) :
    (transposePacking p).square i = S12.pullSwap (p.square i) := rfl

/-- Every square moves together, without independently relabeling an owner. -/
theorem transpose_inside (p : S12.NormalizedPacking) (i : Fin 12) (x y : ℝ) :
    ((transposePacking p).square i).Inside x y ↔ (p.square i).Inside y x := by
  rw [transpose_square, S12.inside_pullSwap]

/-- The actual marker code is transported, rather than assigned by hand. -/
theorem transpose_code (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) (i : Fin 12) :
    S12.markerCode (transposePacking p) i = transpose.maskAction (S12.markerCode p i) := by
  have hm : S12.markerCode p i ∈ family := by
    rw [← hf]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hc := S12.mask_action_spec transpose transpose_mem (S12.markerCode p i)
    (S12.markerCode_spec p i).1
  have he : S12.ExactMarkers (p.square i)
      (S12.maskSupport (transpose.maskAction (transpose.maskAction (S12.markerCode p i)))) := by
    rw [transpose_mask_involution _ hm]
    exact S12.coded_exact p i
  have hnew := S12.exact_markers_pull transpose transpose_mem (p.square i)
    (transpose.maskAction (S12.markerCode p i)) hc.1 he
  have hsupport : S12.maskSupport (S12.markerCode (transposePacking p) i) =
      S12.maskSupport (transpose.maskAction (S12.markerCode p i)) := by
    apply Finset.ext
    intro j
    exact (S12.coded_exact (transposePacking p) i j).symm.trans (hnew j)
  exact S12.candidate_support_injective _ _
    (S12.markerCode_spec (transposePacking p) i).1 hc.1 hsupport

/-- Transposition preserves the complete actual case family. -/
theorem transpose_family (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    S12.codedMarkerFamily (transposePacking p) = family := by
  have he : S12.codedMarkerFamily (transposePacking p) =
      (S12.codedMarkerFamily p).image transpose.maskAction := by
    unfold S12.codedMarkerFamily
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i _
    exact transpose_code p hf i
  rw [he, hf, transpose_family_masks]

theorem transpose_code_one (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) (i : Fin 12)
    (hi : S12.markerCode p i = 1) : S12.markerCode (transposePacking p) i = 2 := by
  rw [transpose_code p hf i, hi]
  decide

theorem transpose_code_two (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) (i : Fin 12)
    (hi : S12.markerCode p i = 2) : S12.markerCode (transposePacking p) i = 1 := by
  rw [transpose_code p hf i, hi]
  decide

theorem code_one_strengthened (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 1) (hz : ¬(p.square i).Inside 1 1) :
    StrengthenedMissingCorner (p.square i) :=
  ⟨code_one_missing_entrance p i hi hz, code_one_anchors p i hi,
    code_one_missing_points p i hi hz⟩

/-- Every realization has a canonical code-1 missing-corner owner, either
    in the original packing or after transposing the entire packing. The
    actual family, every other square and the original owner indices move
    together. This reduces two root contradictions to a single universal
    root contradiction; it does not prove that contradiction. -/
theorem canonical_missing_corner_cover (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ q : S12.NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ S12.codedMarkerFamily q = family ∧
      ∃ i j : Fin 12,
        S12.markerCode q i = 1 ∧ S12.markerCode q j = 2 ∧ i ≠ j ∧
        StrengthenedMissingCorner (q.square i) := by
  obtain ⟨i, j, hi, hj, hij, _, _, hroot⟩ := corner_roots p hf
  rcases hroot with hmissing | ⟨_, hmissing⟩
  · exact ⟨p, Or.inl rfl, hf, i, j, hi, hj, hij,
      code_one_strengthened p i hi hmissing⟩
  · have hi' := transpose_code_two p hf j hj
    have hj' := transpose_code_one p hf i hi
    have hz' : ¬((transposePacking p).square j).Inside 1 1 := by
      intro h
      exact hmissing ((transpose_inside p j 1 1).mp h)
    exact ⟨transposePacking p, Or.inr rfl, transpose_family p hf,
      j, i, hi', hj', hij.symm, code_one_strengthened _ j hi' hz'⟩

theorem retained_canonical_missing_corner_cover
    (r : S12.CoverRow) (hr : r ∈ S12.retainedRows) (hid : r.originalId = 977)
    (p : S12.NormalizedPacking) (hf : S12.codedMarkerFamily p = r.groups) :
    ∃ q : S12.NormalizedPacking,
      (q = p ∨ q = transposePacking p) ∧ S12.codedMarkerFamily q = family ∧
      ∃ i j : Fin 12,
        S12.markerCode q i = 1 ∧ S12.markerCode q j = 2 ∧ i ≠ j ∧
        StrengthenedMissingCorner (q.square i) :=
  canonical_missing_corner_cover p (hf.trans (row_family r hr hid))

/-- One complete canonical root contradiction suffices for the all-row
    case contract. This remaining premise still quantifies over arbitrary
    normalized packings and the entire actual marker family. -/
theorem excludes_case_of_canonical_corner_root
    (hroot : ∀ (p : S12.NormalizedPacking) (i j : Fin 12),
      S12.codedMarkerFamily p = family →
      S12.markerCode p i = 1 → S12.markerCode p j = 2 → i ≠ j →
      StrengthenedMissingCorner (p.square i) → False) :
    ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨q, _, hq, i, j, hi, hj, hij, hmissing⟩ := canonical_missing_corner_cover p hf
  exact hroot q i j hq hi hj hij hmissing

end S12Completion.C977

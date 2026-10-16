import Completion.Cases.C977.WallBranches

namespace S12Completion.C977
open S12 S12Pilot

/-- Re-indexing faces preserves the actual square, its side and its center.
    The positive normal components impose no orientation restriction. -/
structure PositiveFrameOf (q r : OpenSquare) : Prop where
  c_nonnegative : 0 ≤ r.c
  s_nonnegative : 0 ≤ r.s
  side_eq : r.side = q.side
  centerX_eq : centerX r = centerX q
  centerY_eq : centerY r = centerY q
  inside_iff : ∀ x y, r.Inside x y ↔ q.Inside x y

theorem positive_frame_of (q : OpenSquare) :
    ∃ r : OpenSquare, PositiveFrameOf q r := by
  obtain ⟨r, hc, hs, ha, hx, hy, hi⟩ := exists_positive_frame q
  exact ⟨r, hc, hs, ha, hx, hy, hi⟩

/-- Closed upper-U contact or exclusion for the unused central marker 10. -/
def TenUpperU (q : OpenSquare) : Prop :=
  q.loU + q.side ≤ q.c * (47 / 20) + q.s * (47 / 20)

/-- Closed upper-V contact or exclusion for marker 10. -/
def TenUpperV (q : OpenSquare) : Prop :=
  q.loV + q.side ≤ -q.s * (47 / 20) + q.c * (47 / 20)

/-- Closed lower-V contact or exclusion for marker 10. -/
def TenLowerV (q : OpenSquare) : Prop :=
  -q.s * (47 / 20) + q.c * (47 / 20) ≤ q.loV

/-- Moving upward from marker 9 to missing marker 10 increases both positive
    frame coordinates. Only the two upper faces can exclude marker 10. -/
theorem marker_nine_ten_faces (q : OpenSquare) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (howned : q.Inside (47 / 20) (33 / 20))
    (hmissing : ¬q.Inside (47 / 20) (47 / 20)) :
    TenUpperU q ∨ TenUpperV q := by
  rcases howned with ⟨hu0, hu1, hv0, hv1⟩
  by_contra h
  simp only [not_or, TenUpperU, TenUpperV, not_le] at h
  apply hmissing
  change InBands q.loU q.loV q.side _ _
  dsimp [InBands]
  exact ⟨by nlinarith only [hu0, hs], h.1,
    by nlinarith only [hv0, hc], h.2⟩

/-- Moving right from marker 11 increases U and decreases V. Its owned
    strict bands rule out the other two faces, including boundary cases. -/
theorem marker_eleven_ten_faces (q : OpenSquare) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (howned : q.Inside (33 / 20) (47 / 20))
    (hmissing : ¬q.Inside (47 / 20) (47 / 20)) :
    TenUpperU q ∨ TenLowerV q := by
  rcases howned with ⟨hu0, hu1, hv0, hv1⟩
  by_contra h
  simp only [not_or, TenUpperU, TenLowerV, not_le] at h
  apply hmissing
  change InBands q.loU q.loV q.side _ _
  dsimp [InBands]
  exact ⟨by nlinarith only [hu0, hc], h.1, h.2,
    by nlinarith only [hv1, hs]⟩

/-- On the closed c≥s orientation half, marker 8 to marker 10 increases
    both bands. Equality of the normal components is retained. -/
theorem marker_eight_ten_faces_ge (q : OpenSquare) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (hcs : q.s ≤ q.c) (howned : q.Inside (33 / 20) (33 / 20))
    (hmissing : ¬q.Inside (47 / 20) (47 / 20)) :
    TenUpperU q ∨ TenUpperV q := by
  rcases howned with ⟨hu0, hu1, hv0, hv1⟩
  by_contra h
  simp only [not_or, TenUpperU, TenUpperV, not_le] at h
  apply hmissing
  change InBands q.loU q.loV q.side _ _
  dsimp [InBands]
  exact ⟨by nlinarith only [hu0, hc, hs], h.1,
    by nlinarith only [hv0, hcs], h.2⟩

/-- On the closed s≥c orientation half, marker 8 to marker 10 increases U
    and decreases V. Equality occurs in this branch as well. -/
theorem marker_eight_ten_faces_le (q : OpenSquare) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (hcs : q.c ≤ q.s) (howned : q.Inside (33 / 20) (33 / 20))
    (hmissing : ¬q.Inside (47 / 20) (47 / 20)) :
    TenUpperU q ∨ TenLowerV q := by
  rcases howned with ⟨hu0, hu1, hv0, hv1⟩
  by_contra h
  simp only [not_or, TenUpperU, TenLowerV, not_le] at h
  apply hmissing
  change InBands q.loU q.loV q.side _ _
  dsimp [InBands]
  exact ⟨by nlinarith only [hu0, hc, hs], h.1, h.2,
    by nlinarith only [hv1, hcs]⟩

/-- At the diagonal orientation the two V coordinates coincide. The strict
    V bands of marker 8 force marker 10 onto the closed upper-U face. -/
theorem marker_eight_ten_faces_eq (q : OpenSquare) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (hcs : q.c = q.s) (howned : q.Inside (33 / 20) (33 / 20))
    (hmissing : ¬q.Inside (47 / 20) (47 / 20)) : TenUpperU q := by
  rcases howned with ⟨hu0, hu1, hv0, hv1⟩
  by_contra h
  have hu : q.c * (47 / 20) + q.s * (47 / 20) < q.loU + q.side :=
    lt_of_not_ge h
  apply hmissing
  change InBands q.loU q.loV q.side _ _
  dsimp [InBands]
  exact ⟨by nlinarith only [hu0, hc, hs], hu,
    by nlinarith only [hv0, hcs], by nlinarith only [hv1, hcs]⟩

/-- The closed orientation split supplies an exhaustive marker-8 face cover.
    The two halves overlap at c=s; neither strict contact is discarded. -/
theorem marker_eight_ten_face_cover (q : OpenSquare) (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (howned : q.Inside (33 / 20) (33 / 20))
    (hmissing : ¬q.Inside (47 / 20) (47 / 20)) :
    (q.s ≤ q.c ∧ (TenUpperU q ∨ TenUpperV q)) ∨
      (q.c ≤ q.s ∧ (TenUpperU q ∨ TenLowerV q)) := by
  rcases le_total q.s q.c with hcs | hcs
  · exact Or.inl ⟨hcs, marker_eight_ten_faces_ge q hc hs hcs howned hmissing⟩
  · exact Or.inr ⟨hcs, marker_eight_ten_faces_le q hc hs hcs howned hmissing⟩

/-- An actual code-512 owner (marker 9) admits the two closed upper-face
    branches. The original label, center, side and all interior points remain
    available through the frame equivalence. -/
theorem code_512_ten_faces (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) (hi : markerCode p i = 512) :
    ∃ r : OpenSquare, PositiveFrameOf (p.square i) r ∧
      (TenUpperU r ∨ TenUpperV r) := by
  have hsupport : maskSupport 512 = {9} := by decide
  have he : ExactMarkers (p.square i) {9} := by
    simpa only [hi, hsupport] using coded_exact p i
  have howned : (p.square i).Inside (47 / 20) (33 / 20) := by
    simpa [Owns, marker] using (he 9).mpr (by simp)
  have hmissing : ¬(p.square i).Inside (47 / 20) (47 / 20) := by
    simpa [Owns, marker] using unused_marker_ten p hf i
  obtain ⟨r, hr⟩ := positive_frame_of (p.square i)
  exact ⟨r, hr, marker_nine_ten_faces r hr.c_nonnegative hr.s_nonnegative
    ((hr.inside_iff _ _).mpr howned)
    (fun h => hmissing ((hr.inside_iff _ _).mp h))⟩

/-- An actual code-2048 owner (marker 11) admits the upper-U/lower-V cover. -/
theorem code_2048_ten_faces (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) (hi : markerCode p i = 2048) :
    ∃ r : OpenSquare, PositiveFrameOf (p.square i) r ∧
      (TenUpperU r ∨ TenLowerV r) := by
  have hsupport : maskSupport 2048 = {11} := by decide
  have he : ExactMarkers (p.square i) {11} := by
    simpa only [hi, hsupport] using coded_exact p i
  have howned : (p.square i).Inside (33 / 20) (47 / 20) := by
    simpa [Owns, marker] using (he 11).mpr (by simp)
  have hmissing : ¬(p.square i).Inside (47 / 20) (47 / 20) := by
    simpa [Owns, marker] using unused_marker_ten p hf i
  obtain ⟨r, hr⟩ := positive_frame_of (p.square i)
  exact ⟨r, hr, marker_eleven_ten_faces r hr.c_nonnegative hr.s_nonnegative
    ((hr.inside_iff _ _).mpr howned)
    (fun h => hmissing ((hr.inside_iff _ _).mp h))⟩

/-- The code-256 owner (marker 8) has an exhaustive closed orientation/face
    cover, and the diagonal tie has the sharper single upper-U conclusion. -/
theorem code_256_ten_faces (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) (hi : markerCode p i = 256) :
    ∃ r : OpenSquare, PositiveFrameOf (p.square i) r ∧
      ((r.s ≤ r.c ∧ (TenUpperU r ∨ TenUpperV r)) ∨
        (r.c ≤ r.s ∧ (TenUpperU r ∨ TenLowerV r))) ∧
      (r.c = r.s → TenUpperU r) := by
  have hsupport : maskSupport 256 = {8} := by decide
  have he : ExactMarkers (p.square i) {8} := by
    simpa only [hi, hsupport] using coded_exact p i
  have howned : (p.square i).Inside (33 / 20) (33 / 20) := by
    simpa [Owns, marker] using (he 8).mpr (by simp)
  have hmissing : ¬(p.square i).Inside (47 / 20) (47 / 20) := by
    simpa [Owns, marker] using unused_marker_ten p hf i
  obtain ⟨r, hr⟩ := positive_frame_of (p.square i)
  have ho := (hr.inside_iff _ _).mpr howned
  have hm : ¬r.Inside (47 / 20) (47 / 20) :=
    fun h => hmissing ((hr.inside_iff _ _).mp h)
  exact ⟨r, hr, marker_eight_ten_face_cover r hr.c_nonnegative hr.s_nonnegative ho hm,
    fun hcs => marker_eight_ten_faces_eq r hr.c_nonnegative hr.s_nonnegative hcs ho hm⟩

end S12Completion.C977

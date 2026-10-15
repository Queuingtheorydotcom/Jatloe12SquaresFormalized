import Completion.Cases.C977.RowIdentity

namespace S12Completion.C977

/-- Every code in the actual marker family names exactly one square. -/
theorem code_owner_unique (p : S12.NormalizedPacking) (m : Nat)
    (hm : m ∈ S12.codedMarkerFamily p) :
    ∃! i : Fin 12, S12.markerCode p i = m := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact S12.markerCode_injective p (hj.trans hi.symm)

/-- Code 1 means ownership of marker 0 and exclusion of every other marker.
    All ownership in this statement is strict interior ownership. -/
theorem code_one_exact (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 1) :
    S12.ExactMarkers (p.square i) {0} := by
  have hs : S12.maskSupport 1 = {0} := by decide
  simpa only [hi, hs] using S12.coded_exact p i

/-- Code 2 means ownership of marker 1 and exclusion of every other marker. -/
theorem code_two_exact (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2) :
    S12.ExactMarkers (p.square i) {1} := by
  have hs : S12.maskSupport 2 = {1} := by decide
  simpa only [hi, hs] using S12.coded_exact p i

/-- The two singleton owners at the lower-left corner are distinct.
    They are extracted from the whole actual family, without choosing a
    relabeling or changing the geometric frame. -/
theorem corner_owners (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      S12.ExactMarkers (p.square i) {0} ∧
      S12.ExactMarkers (p.square j) {1} := by
  have h1 : 1 ∈ S12.codedMarkerFamily p := by
    rw [hf]
    decide
  have h2 : 2 ∈ S12.codedMarkerFamily p := by
    rw [hf]
    decide
  obtain ⟨i, hi, _⟩ := code_owner_unique p 1 h1
  obtain ⟨j, hj, _⟩ := code_owner_unique p 2 h2
  have hij : i ≠ j := by
    intro he
    have hn : (1 : Nat) = 2 := hi.symm.trans ((congrArg (S12.markerCode p) he).trans hj)
    exact (by decide : (1 : Nat) ≠ 2) hn
  exact ⟨i, j, hi, hj, hij, code_one_exact p i hi, code_two_exact p j hj⟩

/-- The exact two-root missing-corner cover used by the case-977 route.
    A point on a square's boundary is not inside, so it is included in
    the missing branch. Root 1 records the present corner for owner i.
    No transposition or wall-sign choice is needed for this cover. -/
theorem missing_corner_cover (p : S12.NormalizedPacking) (i j : Fin 12)
    (hij : i ≠ j) :
    ¬(p.square i).Inside 1 1 ∨
      ((p.square i).Inside 1 1 ∧ ¬(p.square j).Inside 1 1) := by
  classical
  by_cases hi : (p.square i).Inside 1 1
  · exact Or.inr ⟨hi, fun hj => p.disjoint i j hij 1 1 ⟨hi, hj⟩⟩
  · exact Or.inl hi

/-- Every actual case-977 family is covered by the two geometric roots,
    with the singleton markers, distinct owners and common frame preserved.
    This is root coverage, not a proof that either root is impossible. -/
theorem corner_roots (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      S12.ExactMarkers (p.square i) {0} ∧
      S12.ExactMarkers (p.square j) {1} ∧
      (¬(p.square i).Inside 1 1 ∨
        ((p.square i).Inside 1 1 ∧ ¬(p.square j).Inside 1 1)) := by
  obtain ⟨i, j, hi, hj, hij, he0, he1⟩ := corner_owners p hf
  exact ⟨i, j, hi, hj, hij, he0, he1, missing_corner_cover p i j hij⟩

/-- The same root cover applies to every retained row with historical ID 977,
    rather than just a chosen row or a finite sample of configurations. -/
theorem retained_corner_roots (r : S12.CoverRow) (hr : r ∈ S12.retainedRows)
    (hid : r.originalId = 977) (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = r.groups) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      S12.ExactMarkers (p.square i) {0} ∧
      S12.ExactMarkers (p.square j) {1} ∧
      (¬(p.square i).Inside 1 1 ∨
        ((p.square i).Inside 1 1 ∧ ¬(p.square j).Inside 1 1)) := by
  apply corner_roots p
  exact hf.trans (row_family r hr hid)

/-- The explicit entrance hypotheses for the missing-corner strengthening.
    The two additional points asserted by Bentz's Lemma 11 are derived in
    MissingCornerPoints.lean from this entrance and SingletonAnchors. -/
structure MissingCornerEntrance (q : S12Pilot.OpenSquare) : Prop where
  side_gt_one : 1 < q.side
  side_le : q.side ≤ 1001 / 1000
  contained : S12.InsideContainer q
  marker_owned : q.Inside 1 (457 / 500)
  opposite_marker_missing : ¬q.Inside (457 / 500) 1
  wall_marker_missing : ¬q.Inside (457 / 500) 2
  inner_marker_missing : ¬q.Inside (33 / 20) (33 / 20)
  corner_missing : ¬q.Inside 1 1

/-- A missing corner for the code-1 singleton supplies every explicit
    point premise of the canonical missing-corner argument. -/
theorem code_one_missing_entrance (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 1) (hc : ¬(p.square i).Inside 1 1) :
    MissingCornerEntrance (p.square i) := by
  have he := code_one_exact p i hi
  have hout : ∀ m : S12.Marker, m ≠ 0 → ¬S12.Owns (p.square i) m := by
    intro m hm ho
    exact hm (Finset.mem_singleton.mp ((he m).mp ho))
  refine ⟨?_, ?_, p.contained i, ?_, ?_, ?_, ?_, hc⟩
  · rw [p.congruent]
    exact p.side_gt_one
  · rw [p.congruent]
    exact p.side_le
  · simpa [S12.Owns, S12.marker] using (he 0).mpr (by simp)
  · simpa [S12.Owns, S12.marker] using hout 1 (by decide)
  · simpa [S12.Owns, S12.marker] using hout 12 (by decide)
  · simpa [S12.Owns, S12.marker] using hout 8 (by decide)

/-- For the code-2 singleton, only the square used in the canonical lemma
    is transposed. Conclusions can be transported back by inside_pullSwap;
    the packing, labels and auxiliary context keep their original frame. -/
theorem code_two_missing_entrance (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2) (hc : ¬(p.square i).Inside 1 1) :
    MissingCornerEntrance (S12.pullSwap (p.square i)) := by
  have he := code_two_exact p i hi
  have hout : ∀ m : S12.Marker, m ≠ 1 → ¬S12.Owns (p.square i) m := by
    intro m hm ho
    exact hm (Finset.mem_singleton.mp ((he m).mp ho))
  refine ⟨?_, ?_, S12.container_pullSwap _ (p.contained i), ?_, ?_, ?_, ?_, ?_⟩
  · change 1 < (p.square i).side
    rw [p.congruent]
    exact p.side_gt_one
  · change (p.square i).side ≤ 1001 / 1000
    rw [p.congruent]
    exact p.side_le
  · simpa [S12.Owns, S12.marker, S12.inside_pullSwap] using
      (he 1).mpr (by simp)
  · simpa [S12.Owns, S12.marker, S12.inside_pullSwap] using hout 0 (by decide)
  · simpa [S12.Owns, S12.marker, S12.inside_pullSwap] using hout 13 (by decide)
  · simpa [S12.Owns, S12.marker, S12.inside_pullSwap] using hout 8 (by decide)
  · simpa only [S12.inside_pullSwap] using hc

/-- Every actual case-977 realization enters one of the two canonical
    missing-corner branches with all geometric entrance hypotheses proved.
    Root 1 additionally preserves owner 0's strict corner ownership. -/
theorem missing_corner_entrance_cover (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      (MissingCornerEntrance (p.square i) ∨
        ((p.square i).Inside 1 1 ∧
          MissingCornerEntrance (S12.pullSwap (p.square j)))) := by
  obtain ⟨i, j, hi, hj, hij, _, _, hroot⟩ := corner_roots p hf
  refine ⟨i, j, hi, hj, hij, ?_⟩
  rcases hroot with hroot | ⟨hpresent, hmissing⟩
  · exact Or.inl (code_one_missing_entrance p i hi hroot)
  · exact Or.inr ⟨hpresent, code_two_missing_entrance p j hj hmissing⟩

/-- Conditional case assembly over the complete two-root cover.
    Each remaining premise must refute every actual normalized packing in
    its root, with the whole marker family and original owner labels kept.
    Neither a local leaf nor a fixed-angle exclusion discharges a premise.
    This theorem does not supply either geometric root contradiction. -/
theorem excludes_case_of_corner_roots
    (hroot0 : ∀ (p : S12.NormalizedPacking) (i j : Fin 12),
      S12.codedMarkerFamily p = family →
      S12.markerCode p i = 1 → S12.markerCode p j = 2 → i ≠ j →
      MissingCornerEntrance (p.square i) → False)
    (hroot1 : ∀ (p : S12.NormalizedPacking) (i j : Fin 12),
      S12.codedMarkerFamily p = family →
      S12.markerCode p i = 1 → S12.markerCode p j = 2 → i ≠ j →
      (p.square i).Inside 1 1 →
      MissingCornerEntrance (S12.pullSwap (p.square j)) → False) :
    ExcludesCase 977 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨i, j, hi, hj, hij, hroot⟩ := missing_corner_entrance_cover p hf
  rcases hroot with hroot | ⟨hpresent, hroot⟩
  · exact hroot0 p i j hf hi hj hij hroot
  · exact hroot1 p i j hf hi hj hij hpresent hroot

end S12Completion.C977

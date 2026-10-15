import Completion.Cases.C977.CornerRoots
import Completion.Cases.C977.MissingCornerGeometry

namespace S12Completion.C977

/-- The code-1 owner receives all three original singleton anchors without
    any assumption about ownership of the corner (1,1). -/
theorem code_one_anchors (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 1) : SingletonAnchors (p.square i) := by
  have he := code_one_exact p i hi
  have hp : S12.Owns (p.square i) 0 := (he 0).mpr (by simp)
  have hout : ∀ m : S12.Marker, m ≠ 0 → ¬S12.Owns (p.square i) m := by
    intro m hm ho
    exact hm (Finset.mem_singleton.mp ((he m).mp ho))
  obtain ⟨h0, h1, h2⟩ := S12.corner_singleton_forces (p.square i)
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained i) hp hout
  exact ⟨h0, h1, h2⟩

/-- Transposition gives the canonical anchors for the code-2 owner, while
    leaving the packing and owner labels in their original frame. -/
theorem code_two_anchors (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2) :
    SingletonAnchors (S12.pullSwap (p.square i)) := by
  have he := code_two_exact p i hi
  have hp : S12.Owns (S12.pullSwap (p.square i)) 0 := by
    simpa [S12.owns_pullSwap, S12.permSwap] using (he 1).mpr (by simp)
  have hout : ∀ m : S12.Marker, m ≠ 0 →
      ¬S12.Owns (S12.pullSwap (p.square i)) m := by
    intro m hm ho
    have hm' : S12.permSwap m = 1 :=
      Finset.mem_singleton.mp ((he _).mp ((S12.owns_pullSwap _ m).mp ho))
    have he0 : S12.permSwap m = S12.permSwap 0 := by
      simpa [S12.permSwap] using hm'
    exact hm (S12.permSwap_injective he0)
  obtain ⟨h0, h1, h2⟩ := S12.corner_singleton_forces
    (S12.pullSwap (p.square i))
    (by change 1 < (p.square i).side; rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square i).side ≤ 1001 / 1000; rw [p.congruent]; exact p.side_le)
    (S12.container_pullSwap _ (p.contained i)) hp hout
  exact ⟨h0, h1, h2⟩

/-- In the original packing frame, the code-2 anchors have their coordinates
    exchanged. Every point in this conclusion is strictly interior. -/
theorem code_two_original_anchors (p : S12.NormalizedPacking) (i : Fin 12)
    (hi : S12.markerCode p i = 2) :
    (p.square i).Inside 1 (28 / 25) ∧
    (p.square i).Inside 1 (87 / 50) ∧
    (p.square i).Inside (19 / 25) (187 / 100) := by
  obtain ⟨h0, h1, h2⟩ := code_two_anchors p i hi
  simpa only [S12.inside_pullSwap] using And.intro h0 (And.intro h1 h2)

/-- Both singleton owners carry their unconditional strict anchors throughout
    the complete two-root cover. The missing-corner entrance and the present
    corner of the second root are preserved exactly. -/
theorem anchored_missing_corner_entrance_cover (p : S12.NormalizedPacking)
    (hf : S12.codedMarkerFamily p = family) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      SingletonAnchors (p.square i) ∧
      SingletonAnchors (S12.pullSwap (p.square j)) ∧
      (MissingCornerEntrance (p.square i) ∨
        ((p.square i).Inside 1 1 ∧
          MissingCornerEntrance (S12.pullSwap (p.square j)))) := by
  obtain ⟨i, j, hi, hj, hij, hroot⟩ := missing_corner_entrance_cover p hf
  exact ⟨i, j, hi, hj, hij, code_one_anchors p i hi, code_two_anchors p j hj, hroot⟩

/-- The anchored cover applies to every retained row with historical ID 977. -/
theorem retained_anchored_missing_corner_entrance_cover
    (r : S12.CoverRow) (hr : r ∈ S12.retainedRows) (hid : r.originalId = 977)
    (p : S12.NormalizedPacking) (hf : S12.codedMarkerFamily p = r.groups) :
    ∃ i j : Fin 12,
      S12.markerCode p i = 1 ∧ S12.markerCode p j = 2 ∧ i ≠ j ∧
      SingletonAnchors (p.square i) ∧
      SingletonAnchors (S12.pullSwap (p.square j)) ∧
      (MissingCornerEntrance (p.square i) ∨
        ((p.square i).Inside 1 1 ∧
          MissingCornerEntrance (S12.pullSwap (p.square j)))) := by
  apply anchored_missing_corner_entrance_cover p
  exact hf.trans (row_family r hr hid)

end S12Completion.C977

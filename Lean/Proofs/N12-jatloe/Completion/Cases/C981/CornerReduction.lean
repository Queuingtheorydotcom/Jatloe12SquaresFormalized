import Completion.Cases.C981.Geometry
import S12.FamilyTransport

namespace S12Completion.C981
open S12 S12Pilot

def diagonal : Transform := ⟨true, false, false⟩

theorem diagonal_mem : diagonal ∈ allTransforms := by decide

theorem diagonal_family : family.image diagonal.maskAction = family := by
  decide

/-- Diagonal reflection preserves this entire family, including its missing
central marker. It acts on the whole packing rather than one local square. -/
theorem diagonal_packing_family (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    codedMarkerFamily (diagonal.pullPacking p) = family := by
  have hc : ∀ m ∈ family, m ∈ candidateMasks := by decide
  have hsub : family ⊆ codedMarkerFamily (diagonal.pullPacking p) := by
    intro m hm
    have hmem : diagonal.maskAction m ∈ codedMarkerFamily p := by
      rw [hf, ← diagonal_family]
      exact Finset.mem_image.mpr ⟨m, hm, rfl⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have he : ExactMarkers (p.square i) (maskSupport (diagonal.maskAction m)) := by
      rw [← hi]
      exact coded_exact p i
    have hnew := exact_markers_pull diagonal diagonal_mem (p.square i) m (hc m hm) he
    have hsupport :
        maskSupport (markerCode (diagonal.pullPacking p) i) = maskSupport m := by
      apply Finset.ext
      intro j
      exact (coded_exact (diagonal.pullPacking p) i j).symm.trans (hnew j)
    have hcode := candidate_support_injective _ _
      (markerCode_spec (diagonal.pullPacking p) i).1 (hc m hm) hsupport
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hcode⟩
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [codedMarkerFamily_card]
  decide

/-- One missing-corner branch suffices: if owner 0 contains (1,1), owner 1
does not, and reflection turns owner 1 into owner 0 in the same case. -/
theorem missing_corner_normal_form (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ q : NormalizedPacking, codedMarkerFamily q = family ∧
      ∃ i : Fin 12, ExactMarkers (q.square i) {0} ∧
        ¬(q.square i).Inside 1 1 := by
  obtain ⟨i, j, hij, _, _, hi, hj⟩ := corner_owners p hf
  rcases disjoint_corner_split (p.square i) (p.square j) 1 1
      (p.disjoint i j hij) with hmiss | ⟨_, hmiss⟩
  · exact ⟨p, hf, i, hi, hmiss⟩
  · refine ⟨diagonal.pullPacking p, diagonal_packing_family p hf, j, ?_, ?_⟩
    · intro k
      change Owns (pullSwap (p.square j)) k ↔ k ∈ ({0} : Finset Marker)
      rw [owns_pullSwap, hj]
      fin_cases k <;> decide
    · change ¬(pullSwap (p.square j)).Inside 1 1
      simpa only [inside_pullSwap] using hmiss

/-- Exact remaining case obligation after the justified symmetry reduction.
The right side is still an unproved geometric exclusion, not a certificate
premise silently discharged by the row identity. -/
theorem excludes_case_iff_missing_corner :
    ExcludesCase 981 ↔
      ∀ p : NormalizedPacking, codedMarkerFamily p = family →
        ∀ i : Fin 12, ExactMarkers (p.square i) {0} →
          ¬(p.square i).Inside 1 1 → False := by
  rw [excludes_case_iff]
  constructor
  · intro h p hp _ _ _
    exact h p hp
  · intro h p hp
    obtain ⟨q, hq, i, hi, hmiss⟩ := missing_corner_normal_form p hp
    exact h q hq i hi hmiss

end S12Completion.C981

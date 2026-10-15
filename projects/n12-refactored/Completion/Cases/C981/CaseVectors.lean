import Completion.Cases.C981.Coverage.Final

namespace S12Completion.C981
open S12 S12Pilot

/-- Kernel finite enumeration must check the complete actual domains against
the literal representatives and their exact transposes. No saved count is trusted. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem complete_vector_coverage : DomainCasesCheck domains coveredVectors := by
  unfold DomainCasesCheck
  rw [Coverage.allowed_exact,Coverage.covered_exact]
  intro a ha
  have valid := N12Compact.PrefixCoverage.enumerate_valid _ _ _ ha
  have allowed := N12Compact.PrefixCoverage.reorder_allowed valid.1
  rw [Coverage.reordered_exact] at allowed
  have final := Coverage.complete_chain.sound [] (N12Compact.PrefixCoverage.reorder a)
    (by simp) allowed (N12Compact.PrefixCoverage.reorder_pairwise a valid.2.1) (by simp)
  have covered := Coverage.final_covered _ (by simpa only [List.nil_append] using final)
  have length : a.length = 12 := valid.1.length_eq
  simpa only [N12Compact.PrefixCoverage.unorder_reorder a length] using covered

theorem ownership_mem_covered (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : ownershipVector p ∈ coveredVectors :=
  domain_cases_sound domains (by decide) (by decide) coveredVectors complete_vector_coverage p hf

theorem diagonal_auxiliary_actual (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    natCombinedOwners (diagonal.pullPacking p)
      (ownerIndex (diagonal.pullPacking p) (ownerMasks i)) =
    transposeAuxiliary (natCombinedOwners p
      (ownerIndex p (ownerMasks (ownerTranspose i)))) :=
  diagonal_auxiliary_eq p hf i _ _ (transposeAuxiliary_subset _)
    (fun j => (transposeAuxiliary_mem _ j).symm) rfl

theorem diagonal_ownershipVector (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ownershipVector (diagonal.pullPacking p) = transposeVector (ownershipVector p) := by
  simp only [ownershipVector, transposeVector]
  congr 1
  funext i
  simpa using diagonal_auxiliary_actual p hf i


theorem representative_transpose_involution :
    ∀ v ∈ representativeVectors, transposeVector (transposeVector v) = v := by
  decide

/-- Proving the 117 representative obligations suffices for the original case.
The reflected branch uses a reflected whole packing, with exact owner and
auxiliary-table transport. -/
theorem excluded_of_representative_proofs
    (h : ∀ v ∈ representativeVectors, ExcludesVector v) : ExcludesCase 981 := by
  apply excludes_case_iff.mpr
  intro p hf
  obtain ⟨v, hv, hp⟩ := List.mem_flatMap.mp (ownership_mem_covered p hf)
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with hp | hp
  · exact h v hv p hf hp
  · apply h v hv (diagonal.pullPacking p) (diagonal_packing_family p hf)
    rw [diagonal_ownershipVector p hf, hp]
    exact representative_transpose_involution v hv

end S12Completion.C981

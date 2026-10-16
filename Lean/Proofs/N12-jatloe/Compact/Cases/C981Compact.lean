import Compact.Cases.C981Registry
import Completion.Cases.C981.CaseVectors

/-! Original C981 classification and symmetry assembly. The representative
registry can be checked independently of the inherited domain certificates.
The complete assembly below uses both the actual-packing domain coverage and
all 117 representative exclusions. Its source does not assume catalogue
coverage, and the old conditional API is retained for existing callers. -/
namespace N12Compact.C981Compact
open S12 S12Completion S12Completion.C981
set_option Elab.async false

/-- Compatibility API for the original conditional assembly. Its `Pending`
argument is now supplied by `pending_closed`; ownership-domain coverage and
packing reflection are derived here from the inherited certificates. -/
theorem excludes_case (pending : Pending) : ExcludesCase 981 := by
  apply excluded_of_representative_proofs
  intro v hv
  rw [Case981.catalogue_indexed] at hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact all_representatives pending i

/-- The certified domains cover the ownership vector of the actual packing.
The finite prefix chain puts that vector in the catalogue or its transpose;
in the latter case the witness is the diagonal reflection of the entire
packing, with its marker family and ownership transported together. -/
theorem catalogue_coverage : Case981.CatalogueCoverage := by
  intro p hf
  obtain ⟨v, hv, hp⟩ := List.mem_flatMap.mp (ownership_mem_covered p hf)
  have hrep := hv
  rw [Case981.catalogue_indexed] at hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · exact ⟨p, hf, i, hp⟩
  · refine ⟨diagonal.pullPacking p, diagonal_packing_family p hf, i, ?_⟩
    rw [diagonal_ownershipVector p hf, hp]
    exact representative_transpose_involution _ hrep

/-- Every slot of the original-model boundary is supplied by the current
whole-vector registry; the historical route partition adds no assumptions. -/
def complete_obligations : Case981.Obligations where
  coverage := catalogue_coverage
  formerlyConnected := fun i _ => all_representatives_complete i
  flat := fun i _ => all_representatives_complete i
  strip := fun i _ => all_representatives_complete i
  border := fun i _ => all_representatives_complete i
  kernel := fun i _ => all_representatives_complete i
  refined := fun i _ => all_representatives_complete i
  split := fun i _ => all_representatives_complete i

/-- Unconditional original-case exclusion, including ownership coverage and
whole-packing symmetry. This concerns original case 981, not all 117 retained
original cases in the global classification. -/
theorem excludes_case_complete : ExcludesCase 981 :=
  Case981.excluded_of_obligations complete_obligations

/-- The same conclusion in the literal original marker-family interface. -/
theorem family_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : False :=
  excludes_case_iff.mp excludes_case_complete p hf

#print axioms excludes_case
#print axioms catalogue_coverage
#print axioms excludes_case_complete
end N12Compact.C981Compact

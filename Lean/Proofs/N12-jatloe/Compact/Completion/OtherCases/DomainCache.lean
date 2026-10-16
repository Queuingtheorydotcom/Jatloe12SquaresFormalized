import Compact.Completion.OtherCases.DomainTransport

/-! Literal data cut between symbolic ownership refinements. The cache is
a checked superset of the genuine domain and preserves its arbitrary-real
packing theorem. It introduces no certificate trust or new search premise. -/
namespace N12Compact.Completion.OtherCases.DomainTransport
open S12
set_option Elab.async false

/-- Check every input row before using its filter membership. The length
and indexed premises include every original candidate, including split ties. -/
theorem filter_subset_of_indexed {α : Type} (input output : List α)
    (keep : α → Bool) (fallback : α) {count : Nat} (length : input.length = count)
    (checked : ∀ index : Fin count,
      keep (input.getD index.val fallback) = true → input.getD index.val fallback ∈ output) :
    ∀ value ∈ input.filter keep, value ∈ output := by
  intro value member
  obtain ⟨original, retained⟩ := List.mem_filter.mp member
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp original
  have bound : index < count := by simpa only [length] using valid
  have value_eq : input.getD index fallback = value := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  have result := checked ⟨index,bound⟩
  rw [value_eq] at result
  exact result retained

def cache {family : Finset Nat} (d : CertifiedDomain family) (mask : Nat)
    (allowed : List (Finset Nat)) (same : d.mask = mask)
    (included : ∀ s ∈ d.allowed, s ∈ allowed) : CertifiedDomain family :=
  ⟨mask,allowed,by
    intro p i hf hi
    exact included _ (d.sound p i hf (hi.trans same.symm))⟩

def cacheNamed {family : Finset Nat} (d : NamedDomain family) (mask : Nat)
    (allowed : List (Finset Nat)) (same : d.val.mask = mask)
    (included : ∀ s ∈ d.val.allowed, s ∈ allowed) : NamedDomain family :=
  ⟨cache d.val mask allowed same included,by simpa only [cache,same] using d.member⟩

end N12Compact.Completion.OtherCases.DomainTransport

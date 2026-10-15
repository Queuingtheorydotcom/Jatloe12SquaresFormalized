import Completion.Cases.C981.RowIdentity
import S12.DisjointCornerSplit

namespace S12Completion.C981
open S12 S12Pilot

/-- The lower-left central marker is unowned by every square in case 981. -/
theorem central_marker_unowned (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    ¬Owns (p.square i) 8 := by
  have hm : markerCode p i ∈ family := by
    rw [← hf]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hmissing : ∀ m ∈ family, (8 : Marker) ∉ maskSupport m := by decide
  intro h
  exact hmissing _ hm ((coded_exact p i 8).mp h)

/-- The two distinct lower-left singleton owners exist in every packing
realizing the family; no independently selected local squares are assumed. -/
theorem corner_owners (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ i j : Fin 12, i ≠ j ∧
      markerCode p i = 1 ∧ markerCode p j = 2 ∧
      ExactMarkers (p.square i) {0} ∧ ExactMarkers (p.square j) {1} := by
  have h0 : (1 : Nat) ∈ codedMarkerFamily p := by
    rw [hf]
    decide
  have h1 : (2 : Nat) ∈ codedMarkerFamily p := by
    rw [hf]
    decide
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h0
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h1
  have hij : i ≠ j := by
    intro he
    subst j
    have hbad : (1 : Nat) = 2 := hi.symm.trans hj
    exact (by decide : (1 : Nat) ≠ 2) hbad
  have hi' := coded_exact p i
  have hj' := coded_exact p j
  rw [hi] at hi'
  rw [hj] at hj'
  have hs0 : maskSupport 1 = ({0} : Finset Marker) := by decide
  have hs1 : maskSupport 2 = ({1} : Finset Marker) := by decide
  refine ⟨i, j, hij, hi, hj, ?_, ?_⟩
  · simpa only [hs0] using hi'
  · simpa only [hs1] using hj'

end S12Completion.C981

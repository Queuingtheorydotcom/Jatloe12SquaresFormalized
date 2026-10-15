import S12.CertifiedDomain
import S12.CertifiedPoint

namespace N12Compact.PointPremises
open S12 S12Pilot

/-- Finite entry checks mention only compulsory points, never a search tree. -/
def Check {family : Finset Nat} (d : CertifiedDomain family)
    (known : List (CertifiedPoint family)) (inside outside : List (ℚ × ℚ)) : Prop :=
  d.mask ∈ family ∧ ∀ owned ∈ d.allowed,
    (∀ P ∈ inside, P ∈ queryInsidePoints d.mask 2 owned ∨
      ∃ k ∈ known, k.mask = d.mask ∧ k.point = P) ∧
    (∀ P ∈ outside, P ∈ queryOutsidePoints d.mask 2 owned ∨
      ∃ k ∈ known, k.mask ≠ d.mask ∧ k.point = P)

instance {family : Finset Nat} (d : CertifiedDomain family)
    (known : List (CertifiedPoint family)) (inside outside : List (ℚ × ℚ)) :
    Decidable (Check d known inside outside) := inferInstanceAs (Decidable (_ ∧ _))

theorem sound {family : Finset Nat} (d : CertifiedDomain family)
    (known : List (CertifiedPoint family)) (inside outside : List (ℚ × ℚ))
    (checked : Check d known inside outside) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (∀ P ∈ inside, (p.square (ownerIndex p d.mask)).Inside P.1 P.2) ∧
    (∀ P ∈ outside, ¬(p.square (ownerIndex p d.mask)).Inside P.1 P.2) := by
  let i := ownerIndex p d.mask
  have hi : markerCode p i = d.mask := ownerIndex_spec p d.mask (by rw [hf]; exact checked.1)
  have ha : 1 < (p.square i).side := by rw [p.congruent]; exact p.side_gt_one
  have hs : (p.square i).side ≤ 1001 / 1000 := by rw [p.congruent]; exact p.side_le
  have he : ExactMarkers (p.square i) (maskSupport d.mask) := by simpa only [hi] using coded_exact p i
  have ho := nat_combined_exact p i
  obtain ⟨insideChecked, outsideChecked⟩ := checked.2 _ (d.sound p i hf hi)
  constructor
  · intro P hP
    rcases insideChecked P hP with h | ⟨k, _, hmask, hpoint⟩
    · exact query_inside_sound d.mask 2 _ (p.square i) ha hs (p.contained i) he ho P h
    · simpa only [hmask, hpoint] using k.sound p hf
  · intro P hP hpin
    rcases outsideChecked P hP with h | ⟨k, _, hmask, hpoint⟩
    · exact query_outside_sound d.mask 2 _ (p.square i) he ho P h hpin
    · have hj : markerCode p (ownerIndex p k.mask) = k.mask :=
        ownerIndex_spec p k.mask (by rw [hf]; exact k.member)
      have hkin := k.sound p hf
      rw [hpoint] at hkin
      apply p.disjoint i (ownerIndex p k.mask) _ P.1 P.2 ⟨hpin, hkin⟩
      intro hij
      exact hmask (hj.symm.trans ((congrArg (markerCode p) hij).symm.trans hi))

#print axioms sound
end N12Compact.PointPremises

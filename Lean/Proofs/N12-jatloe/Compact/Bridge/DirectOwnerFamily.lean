import Compact.Bridge.DirectPoseCover
import Compact.Bridge.PointPremises

/-! Shared original-packing entrance for every direct owner cover.

Each record binds an independently valid ownership domain and its actual
point premises to a complete continuous-angle cover. Its output is exactly
the historical reduced pose list, rather than a newly weakened enclosure.
The angle grid is unrestricted; empty angle intervals remain in the checked
owner's roots and are excluded by their numerical proofs.
-/

namespace N12Compact.DirectPoseCover
open S12 S12Pilot

structure CertifiedOwner (family : Finset Nat)
    (known : List (CertifiedPoint family)) where
  domain : CertifiedDomain family
  enclosure : Owner
  enclosure_checked : enclosure.Check
  premises_checked : PointPremises.Check domain known enclosure.inside enclosure.outside
  target : List PoseLeaf
  target_exact : enclosure.leaves = target

/-- The geometric and ownership entrance proof is shared across every owner
and every case. No point ownership or continuous coverage is assumed of p. -/
theorem CertifiedOwner.sound {family : Finset Nat}
    {known : List (CertifiedPoint family)} (owner : CertifiedOwner family known)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    OrientedPoseCovered owner.target (p.square (ownerIndex p owner.domain.mask)) := by
  obtain ⟨inside, outside⟩ := PointPremises.sound owner.domain known
    owner.enclosure.inside owner.enclosure.outside owner.premises_checked p hf
  rw [← owner.target_exact]
  exact owner.enclosure.oriented_sound owner.enclosure_checked _
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _) inside outside

/-- All listed owner covers follow from the same original packing. A later
propagation proof chooses the exact owner entries required by its full chain. -/
theorem certified_owners_sound {family : Finset Nat}
    {known : List (CertifiedPoint family)} (owners : List (CertifiedOwner family known))
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    ∀ owner ∈ owners,
      OrientedPoseCovered owner.target (p.square (ownerIndex p owner.domain.mask)) := by
  intro owner _
  exact owner.sound p hf

#print axioms CertifiedOwner.sound
#print axioms certified_owners_sound
end N12Compact.DirectPoseCover

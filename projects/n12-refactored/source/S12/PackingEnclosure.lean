import S12.ContinuousCertificate
import S12.CertifiedPoint
namespace S12
open S12Pilot
set_option maxHeartbeats 0

/-- Ownership interface for a complete centre/angle enclosure. Each outside
point is justified either by exact ownership or by a different square's hull. -/
structure PackingEnclosure (family : Finset Nat) where
  known : List (CertifiedPoint family)
  mask : Nat
  owned : Finset Nat
  enclosure : {w : OwnerEnclosure // w.Check}

def PackingEnclosure.Check {family : Finset Nat} (w : PackingEnclosure family) : Prop :=
  w.mask∈family ∧
  (∀ P∈w.enclosure.val.inside,P∈queryInsidePoints w.mask 2 w.owned) ∧
  KnownOutsideCheck family w.mask w.owned w.known w.enclosure.val.outside
instance PackingEnclosure.decidableCheck {family : Finset Nat} (w : PackingEnclosure family) : Decidable w.Check :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem PackingEnclosure.sound {family : Finset Nat} (w : PackingEnclosure family)
    (hw : w.Check) (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (ho : natCombinedOwners p (ownerIndex p w.mask)=w.owned) :
    PoseCovered w.enclosure.val.leaves (p.square (ownerIndex p w.mask)) := by
  let i := ownerIndex p w.mask
  have hi : markerCode p i=w.mask := ownerIndex_spec p w.mask (by rw [hf]; exact hw.1)
  have he : ExactMarkers (p.square i) (maskSupport w.mask) := by
    simpa only [hi] using coded_exact p i
  have hx : AuxExact (p.square i) 2 w.owned := by
    simpa only [i,ho] using nat_combined_exact p i
  have ha : 1<(p.square i).side := by rw [p.congruent]; exact p.side_gt_one
  have hs : (p.square i).side≤1001/1000 := by rw [p.congruent]; exact p.side_le
  have hinside := query_inside_sound w.mask 2 w.owned (p.square i) ha hs (p.contained i) he hx
  have houtside := known_outside_sound family w.mask w.owned w.known _ hw.2.2 p hf i hi hx
  exact w.enclosure.val.sound w.enclosure.property (p.square i) ha hs (p.contained i)
    (fun P hP => hinside P (hw.2.1 P hP)) houtside

theorem packing_owners_disjoint (p : NormalizedPacking) (a b : Nat)
    (ha : a∈codedMarkerFamily p) (hb : b∈codedMarkerFamily p) (hne : a≠b) :
    ∀ x y,¬((p.square (ownerIndex p a)).Inside x y ∧
      (p.square (ownerIndex p b)).Inside x y) := by
  apply p.disjoint
  intro h
  apply hne
  exact (ownerIndex_spec p a ha).symm.trans
    ((congrArg (markerCode p) h).trans (ownerIndex_spec p b hb))

#print axioms PackingEnclosure.sound
end S12

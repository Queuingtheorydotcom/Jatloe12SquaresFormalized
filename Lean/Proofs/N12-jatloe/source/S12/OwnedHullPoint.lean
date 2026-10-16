import S12.CertifiedPoint
namespace S12
open S12Pilot
set_option maxHeartbeats 0

/-- A hull point whose proof is valid under a specified auxiliary-owner value.
Unlike CertifiedPoint, this does not assert that the value is globally forced. -/
structure OwnedHullPoint where
  mask : Nat
  owned : Finset Nat
  triangle : TriangleCertificate

def OwnedHullPoint.Check (w : OwnedHullPoint) (family : Finset Nat) : Prop :=
  w.mask∈family ∧ w.triangle.Check ∧
  w.triangle.p0∈queryInsidePoints w.mask 2 w.owned ∧
  w.triangle.p1∈queryInsidePoints w.mask 2 w.owned ∧
  w.triangle.p2∈queryInsidePoints w.mask 2 w.owned
instance OwnedHullPoint.decidableCheck (w : OwnedHullPoint) (family : Finset Nat) : Decidable (w.Check family) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem OwnedHullPoint.sound (w : OwnedHullPoint) (family : Finset Nat) (hw : w.Check family)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (ho : natCombinedOwners p (ownerIndex p w.mask)=w.owned) :
    (p.square (ownerIndex p w.mask)).Inside w.triangle.target.1 w.triangle.target.2 := by
  let i := ownerIndex p w.mask
  have hi : markerCode p i=w.mask := ownerIndex_spec p w.mask (by rw [hf]; exact hw.1)
  have ha : 1<(p.square i).side := by rw [p.congruent]; exact p.side_gt_one
  have hs : (p.square i).side≤1001/1000 := by rw [p.congruent]; exact p.side_le
  have he : ExactMarkers (p.square i) (maskSupport w.mask) := by simpa only [hi] using coded_exact p i
  have hx : AuxExact (p.square i) 2 w.owned := by simpa only [i,ho] using nat_combined_exact p i
  have hp := query_inside_sound w.mask 2 w.owned (p.square i) ha hs (p.contained i) he hx
  exact triangle_certificate_sound w.triangle hw.2.1 (p.square i)
    (hp _ hw.2.2.1) (hp _ hw.2.2.2.1) (hp _ hw.2.2.2.2)

end S12

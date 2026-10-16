import S12.CoreExclusion
namespace S12
open S12Pilot
set_option maxHeartbeats 0

/-- A rational point with proved ownership in every packing of a marker family. -/
structure CertifiedPoint (family : Finset Nat) where
  mask : Nat
  point : ℚ × ℚ
  member : mask∈family
  sound : ∀ p : NormalizedPacking,codedMarkerFamily p=family →
    (p.square (ownerIndex p mask)).Inside point.1 point.2

def CertifiedPoint.ofHull (family : Finset Nat) (mask : Nat) (hm : mask∈family)
    (owned : Finset Nat)
    (forced : ∀ p : NormalizedPacking,codedMarkerFamily p=family →
      natCombinedOwners p (ownerIndex p mask)=owned)
    (w : TriangleCertificate) (hw : w.Check)
    (h0 : w.p0∈queryInsidePoints mask 2 owned)
    (h1 : w.p1∈queryInsidePoints mask 2 owned)
    (h2 : w.p2∈queryInsidePoints mask 2 owned) : CertifiedPoint family :=
  ⟨mask,w.target,hm,by
    intro p hf
    let i := ownerIndex p mask
    have hi : markerCode p i=mask := ownerIndex_spec p mask (by rw [hf]; exact hm)
    have ha : 1<(p.square i).side := by rw [p.congruent]; exact p.side_gt_one
    have hs : (p.square i).side≤1001/1000 := by rw [p.congruent]; exact p.side_le
    have he := coded_exact p i
    rw [hi] at he
    have ho : AuxExact (p.square i) 2 owned := by
      have hh := nat_combined_exact p i
      simpa only [i,forced p hf] using hh
    have hall := query_inside_sound mask 2 owned (p.square i) ha hs (p.contained i) he ho
    exact triangle_certificate_sound w hw (p.square i) (hall w.p0 h0) (hall w.p1 h1) (hall w.p2 h2)⟩

def KnownOutsideCheck (family : Finset Nat) (mask : Nat) (owned : Finset Nat)
    (known : List (CertifiedPoint family)) (points : List (ℚ × ℚ)) : Prop :=
  ∀ P∈points,P∈queryOutsidePoints mask 2 owned ∨ ∃ k∈known,k.mask≠mask ∧ k.point=P
instance decidableKnownOutsideCheck (family : Finset Nat) (mask : Nat) (owned : Finset Nat)
    (known : List (CertifiedPoint family)) (points : List (ℚ × ℚ)) :
    Decidable (KnownOutsideCheck family mask owned known points) :=
  inferInstanceAs (Decidable (∀ P∈points,_))

theorem known_outside_sound (family : Finset Nat) (mask : Nat) (owned : Finset Nat)
    (known : List (CertifiedPoint family)) (points : List (ℚ × ℚ))
    (hcheck : KnownOutsideCheck family mask owned known points)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) (i : Fin 12)
    (hi : markerCode p i=mask) (ho : AuxExact (p.square i) 2 owned) :
    ∀ P∈points,¬(p.square i).Inside P.1 P.2 := by
  intro P hP hinside
  rcases hcheck P hP with h | ⟨k,_,hne,he⟩
  · exact query_outside_sound mask 2 owned (p.square i)
      (by simpa only [hi] using coded_exact p i) ho P h hinside
  · have hj : markerCode p (ownerIndex p k.mask)=k.mask :=
      ownerIndex_spec p k.mask (by rw [hf]; exact k.member)
    have hinside' := k.sound p hf
    rw [he] at hinside'
    apply p.disjoint i (ownerIndex p k.mask) _ P.1 P.2 ⟨hinside,hinside'⟩
    intro hij
    exact hne (hj.symm.trans ((congrArg (markerCode p) hij).symm.trans hi))

#print axioms CertifiedPoint.ofHull
#print axioms known_outside_sound
end S12

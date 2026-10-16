import S12.OwnedHullPoint
import S12.DomainRefinement
namespace S12
set_option maxHeartbeats 0

/-- A common hull point is certified for every allowed auxiliary value.
No globally forced ownership value is required. -/
def DomainHullCheck {family : Finset Nat} (d : CertifiedDomain family)
    (point : ℚ × ℚ) (ws : List {w : OwnedHullPoint // w.Check family}) : Prop :=
  ∀ x∈d.allowed,∃ w∈ws,w.val.mask=d.mask ∧ w.val.owned=x ∧ w.val.triangle.target=point
instance decidableDomainHullCheck {family : Finset Nat} (d : CertifiedDomain family)
    (point : ℚ × ℚ) (ws : List {w : OwnedHullPoint // w.Check family}) :
    Decidable (DomainHullCheck d point ws) := inferInstanceAs (Decidable (∀ x∈_,_))

def CertifiedPoint.ofDomainHull {family : Finset Nat} (d : CertifiedDomain family)
    (hm : d.mask∈family) (point : ℚ × ℚ)
    (ws : List {w : OwnedHullPoint // w.Check family}) (hc : DomainHullCheck d point ws) :
    CertifiedPoint family :=
  ⟨d.mask,point,hm,by
    intro p hf
    have hi : markerCode p (ownerIndex p d.mask)=d.mask :=
      ownerIndex_spec p d.mask (by rw [hf]; exact hm)
    obtain ⟨w,_,hmask,howned,hpoint⟩ := hc _ (d.sound p _ hf hi)
    have ho : natCombinedOwners p (ownerIndex p w.val.mask)=w.val.owned := by
      rw [hmask,howned]
    have hp := w.val.sound family w.property p hf ho
    simpa only [hmask,hpoint] using hp⟩

#print axioms CertifiedPoint.ofDomainHull
end S12

import Compact.Bridge.RelaxedOwnerDomain
import S12.DomainSpecData

/-! The merged-lower families need only nine complete auxiliary-owner domains.
The three omitted owners remain present in the original packing; dropping their
domains only enlarges the finite cover. No refined numerical domain is assumed. -/
namespace N12Compact.MergedLower
open S12 RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def direct (family : Finset Nat) (w : CombinedSpec) (hw : w.Check)
    (hF : Bounds family w.mask w.first.val 0)
    (hG : Bounds family w.mask w.second.val 1)
    (hcount : (family ∩ auxExempt 0).card = 2)
    (hne : w.mask ∉ auxExempt 0) : CertifiedDomain family :=
  restrictFCardOne family (ofCombined family w hw hF hG) hcount hne

def reflectedAllowed (w : CombinedSpec) : List (Finset Nat) :=
  ((w.first.val.allowed.product w.second.val.allowed).filter (fun xy =>
    decide (combinedOwners xy.1 xy.2 ∈ w.allowed))).map (fun xy =>
    combinedOwners (pushOwners reflectXF xy.1) (pushOwners reflectXG xy.2))

theorem reflectedAllowed_mem (w : CombinedSpec) (x y : Finset Nat)
    (hx : x ∈ w.first.val.allowed) (hy : y ∈ w.second.val.allowed)
    (hxy : combinedOwners x y ∈ w.allowed) :
    combinedOwners (pushOwners reflectXF x) (pushOwners reflectXG y) ∈
      reflectedAllowed w := by
  apply List.mem_map.mpr
  refine ⟨(x,y),?_,rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_product.mpr ⟨hx,hy⟩,decide_eq_true hxy⟩

def reflected (family : Finset Nat) (mask : Nat) (w : CombinedSpec) (hw : w.Check)
    (hm : w.mask ∈ candidateMasks)
    (hmask : (⟨false,true,false⟩ : Transform).maskAction w.mask = mask)
    (hF : Bounds family mask w.first.val 0)
    (hG : Bounds family mask w.second.val 1)
    (hcount : (family ∩ auxExempt 0).card = 2)
    (hne : mask ∉ auxExempt 0) : CertifiedDomain family :=
  restrictFCardOne family
    (ofTransformedCombined family mask ⟨false,true,false⟩ (by decide +kernel)
      w hw hm hmask reflectXF reflectXG reflectXF_points reflectXG_points hF hG
      (reflectedAllowed w) (fun x hx y hy hxy => reflectedAllowed_mem w x y hx hy hxy))
    hcount hne

def halfturnedAllowed (w : CombinedSpec) : List (Finset Nat) :=
  ((w.first.val.allowed.product w.second.val.allowed).filter (fun xy =>
    decide (combinedOwners xy.1 xy.2 ∈ w.allowed))).map (fun xy =>
    combinedOwners (pushOwners halfTurnPerm xy.1) (pushOwners halfTurnPerm xy.2))

theorem halfturnedAllowed_mem (w : CombinedSpec) (x y : Finset Nat)
    (hx : x ∈ w.first.val.allowed) (hy : y ∈ w.second.val.allowed)
    (hxy : combinedOwners x y ∈ w.allowed) :
    combinedOwners (pushOwners halfTurnPerm x) (pushOwners halfTurnPerm y) ∈
      halfturnedAllowed w := by
  apply List.mem_map.mpr
  refine ⟨(x,y),?_,rfl⟩
  exact List.mem_filter.mpr ⟨List.mem_product.mpr ⟨hx,hy⟩,decide_eq_true hxy⟩

def halfturned (family : Finset Nat) (mask : Nat) (w : CombinedSpec) (hw : w.Check)
    (hm : w.mask ∈ candidateMasks)
    (hmask : (⟨false,true,true⟩ : Transform).maskAction w.mask = mask)
    (hF : Bounds family mask w.first.val 0)
    (hG : Bounds family mask w.second.val 1)
    (hcount : (family ∩ auxExempt 0).card = 2)
    (hne : mask ∉ auxExempt 0) : CertifiedDomain family :=
  restrictFCardOne family
    (ofTransformedCombined family mask ⟨false,true,true⟩ (by decide +kernel)
      w hw hm hmask halfTurnPerm halfTurnPerm halfTurnF_points halfTurnG_points hF hG
      (halfturnedAllowed w) (fun x hx y hy hxy => halfturnedAllowed_mem w x y hx hy hxy))
    hcount hne

end
end N12Compact.MergedLower

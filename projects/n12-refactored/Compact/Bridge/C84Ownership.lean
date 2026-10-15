import Compact.Bridge.C84MergedBottomDomain
import Compact.Bridge.ForcedAuxiliary
import Compact.Cases.MergedLower.Helpers

/-! Original ownership entrance for case84. The F-budget has THREE exempt
owners, so ordinary owners may have two F points and the merged left pair
may have one. Only the G-budget is a singleton budget. The finite cover
deliberately omits the two paired corner owners; it remains a relaxation
of every original packing. -/
namespace N12Compact.C84Ownership
open S12 S12Pilot RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

def family : Finset Nat := {1,2,4,8,48,192,1024,2304,4096,8704,16384,32768}

private def direct (w : CombinedSpec) (hw : w.Check)
    (hF : Bounds family w.mask w.first.val 0)
    (hG : Bounds family w.mask w.second.val 1) : CertifiedDomain family :=
  restrictByBudget family (ofCombined family w hw hF hG)

private def reflected (mask : Nat) (w : CombinedSpec) (hw : w.Check)
    (hm : w.mask∈candidateMasks)
    (hmask : (⟨false,true,false⟩ : Transform).maskAction w.mask=mask)
    (hF : Bounds family mask w.first.val 0)
    (hG : Bounds family mask w.second.val 1) : CertifiedDomain family :=
  restrictByBudget family
    (ofTransformedCombined family mask ⟨false,true,false⟩ (by decide +kernel)
      w hw hm hmask reflectXF reflectXG reflectXF_points reflectXG_points hF hG
      (MergedLower.reflectedAllowed w)
      (fun x hx y hy hxy => MergedLower.reflectedAllowed_mem w x y hx hy hxy))

private def domain1 := direct combinedSpec1 combinedSpec1_checked
  (by decide +kernel) (by decide +kernel)
private def domain4 := reflected 4 combinedSpec1 combinedSpec1_checked
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def domain2 := direct combinedSpec3 combinedSpec3_checked
  (by decide +kernel) (by decide +kernel)
private def domain8 := reflected 8 combinedSpec3 combinedSpec3_checked
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def domain32768 := direct combinedSpec24 combinedSpec24_checked
  (by decide +kernel) (by decide +kernel)
private def domain4096 := direct combinedSpec17 combinedSpec17_checked
  (by decide +kernel) (by decide +kernel)
private def domain16384 := direct combinedSpec21 combinedSpec21_checked
  (by decide +kernel) (by decide +kernel)
private def domain1024 := reflected 1024 combinedSpec13 combinedSpec13_checked
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def domain8704 : CertifiedDomain family :=
  OwnerBudget.product family 8704
    (ofSmallBudget family 8704 0 (by decide +kernel))
    (C84MergedBottomDomain.domain family (by decide +kernel))
private def domain2304 : CertifiedDomain family :=
  OwnerBudget.product family 2304
    (ofSmallBudget family 2304 0 (by decide +kernel))
    (OwnerBudget.HalfDomain.singleton family 2304 1
      (by decide +kernel) (by decide +kernel))

def domains : List (CertifiedDomain family) :=
  [domain1,domain4,domain2,domain8,domain32768,domain4096,domain16384,
    domain1024,domain8704,domain2304]

theorem members : ∀ d∈domains,d.mask∈family := by decide +kernel
theorem distinct : domains.Pairwise (fun a b => a.mask≠b.mask) := by decide +kernel

/-- These are the complete original G assignments. The two F entries
listed for the walls and corners are likewise common to the whole cover;
no other optional F point is discarded. -/
def forcedPoints : List (Nat × Nat) :=
  [(1,2),(1,12),(4,6),(4,15),(2,0),(2,10),(8,8),(8,18),
   (32768,3),(32768,14),(4096,1),(4096,11),(16384,9),(16384,19),
   (1024,17),(8704,16),(2304,13)]

theorem forced_checked : ∀ item∈forcedPoints,
    feasible (ForcedAuxiliary.withoutPoint domains item.1 item.2) ∅=false := by
  decide +kernel

theorem forced (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask index : Nat) (h : (mask,index)∈forcedPoints) :
    index∈natCombinedOwners p (ownerIndex p mask) :=
  ForcedAuxiliary.contains domains members distinct mask index
    (forced_checked _ h) p hf

noncomputable def owner (p : NormalizedPacking) (mask : Nat) : OpenSquare :=
  p.square (ownerIndex p mask)

theorem point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask index : Nat) (h : (mask,index)∈forcedPoints) (bound : index<20) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (nat_combined_exact p (ownerIndex p mask) index
    (by change index∈List.range 20; exact List.mem_range.mpr bound)).mpr
      (forced p hf mask index h)

theorem owner_code (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) : markerCode p (ownerIndex p mask)=mask :=
  ownerIndex_spec p mask (by rw [hf]; exact member)

theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n) :
    ∀ x y, ¬((owner p m).Inside x y ∧ (owner p n).Inside x y) := by
  apply p.disjoint
  intro equal
  exact different ((owner_code p hf m hm).symm.trans
    ((congrArg (markerCode p) equal).trans (owner_code p hf n hn)))

#print axioms forced
end
end N12Compact.C84Ownership

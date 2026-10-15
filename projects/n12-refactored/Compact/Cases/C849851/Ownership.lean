import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! The original 849/851 families have one necessary complete ownership
assignment. The merged top owner needs no new geometric domain certificate:
the true packing budget gives all ten singleton choices in each auxiliary
grid, and the other actual owners force its unique remaining choice.
No archived pose, assumed auxiliary signature, or native tactic is used here.
The imported historical domain certificates retain their existing trust model.
-/
namespace N12Compact.C849851
open S12 S12Pilot OwnerBudget
set_option Elab.async false
set_option maxRecDepth 10000

def rightMask (merged : Bool) : Nat := if merged then 16416 else 16384

def family (merged : Bool) : Finset Nat :=
  {1,2,12,16,192,256,512,1024,4096,8192,rightMask merged,34816}

private def domain1 (b : Bool) : CertifiedDomain (family b) :=
  CertifiedDomain.ofCombined (family b) combinedSpec0 combinedSpec0_checked
    (by cases b <;> decide +kernel)

private def domain2 (b : Bool) : CertifiedDomain (family b) :=
  CertifiedDomain.ofCombined (family b) combinedSpec2 combinedSpec2_checked
    (by cases b <;> decide +kernel)

private def domain16 (b : Bool) : CertifiedDomain (family b) :=
  OwnerBudget.product (family b) 16
    (HalfDomain.ofSpec (family b) singleSpec14 0 singleSpec14_checked
      (by cases b <;> decide +kernel))
    (HalfDomain.ofSpec (family b) singleSpec16 1 singleSpec16_checked
      (by cases b <;> decide +kernel))

private def domain256 (b : Bool) : CertifiedDomain (family b) :=
  CertifiedDomain.ofCombined (family b) combinedSpec5 combinedSpec5_checked
    (by cases b <;> decide +kernel)

private def domain512 (b : Bool) : CertifiedDomain (family b) :=
  CertifiedDomain.ofCombined (family b) combinedSpec7 combinedSpec7_checked
    (by cases b <;> decide +kernel)

private def domain1024 (b : Bool) : CertifiedDomain (family b) :=
  OwnerBudget.product (family b) 1024
    (HalfDomain.ofSpec (family b) singleSpec34 0 singleSpec34_checked
      (by cases b <;> decide +kernel))
    (HalfDomain.ofSpec (family b) singleSpec35 1 singleSpec35_checked
      (by cases b <;> decide +kernel))

private def domain4096 (b : Bool) : CertifiedDomain (family b) :=
  CertifiedDomain.ofCombined (family b) combinedSpec16 combinedSpec16_checked
    (by cases b <;> decide +kernel)

private def domain8192 (b : Bool) : CertifiedDomain (family b) :=
  CertifiedDomain.ofCombined (family b) combinedSpec18 combinedSpec18_checked
    (by cases b <;> decide +kernel)

private def domainRight : (b : Bool) → CertifiedDomain (family b)
  | false => CertifiedDomain.ofCombined (family false) combinedSpec20
      combinedSpec20_checked (by decide +kernel)
  | true => OwnerBudget.product (family true) 16416
      (HalfDomain.ofSpec (family true) singleSpec82 0 singleSpec82_checked (by decide +kernel))
      (HalfDomain.ofSpec (family true) singleSpec83 1 singleSpec83_checked (by decide +kernel))

private def domain34816 (b : Bool) : CertifiedDomain (family b) :=
  OwnerBudget.product (family b) 34816
    (HalfDomain.singleton (family b) 34816 0
      (by cases b <;> decide +kernel) (by decide +kernel))
    (HalfDomain.singleton (family b) 34816 1
      (by cases b <;> decide +kernel) (by decide +kernel))

def domains (b : Bool) : List (CertifiedDomain (family b)) :=
  [domain1 b,domain2 b,domain16 b,domain4096 b,domain8192 b,
    domain256 b,domain512 b,domain1024 b,domainRight b,domain34816 b]

theorem domains_members (b : Bool) : ∀ d ∈ domains b, d.mask ∈ family b := by
  cases b <;> decide +kernel

theorem domains_distinct (b : Bool) :
    (domains b).Pairwise (fun a c => a.mask ≠ c.mask) := by
  cases b <;> decide +kernel

def masks (b : Bool) : Fin 10 → Nat :=
  ![1,2,16,4096,8192,256,512,1024,rightMask b,34816]

def owned : Fin 10 → Finset Nat :=
  ![{2,12},{0,10},{7,17},{1,11},{6,15},{4,13},{8,18},{5,16},{9,19},{3,14}]

theorem forced_checked (b : Bool) (i : Fin 10) :
    feasible (forcedDomains (domains b) (masks b i) (owned i)) ∅ = false := by
  cases b <;> fin_cases i <;> decide +kernel

/-- All ten facts concern the owners in the same original packing. -/
theorem forced (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 10) :
    natCombinedOwners p (ownerIndex p (masks b i)) = owned i :=
  certified_domain_forced (domains b) (domains_members b) (domains_distinct b)
    (masks b i) (owned i) (forced_checked b i) p hf

noncomputable def owner (b : Bool) (p : NormalizedPacking) (i : Fin 10) : OpenSquare :=
  p.square (ownerIndex p (masks b i))

theorem owner_code (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 10) :
    markerCode p (ownerIndex p (masks b i)) = masks b i :=
  ownerIndex_spec p _ (by rw [hf]; cases b <;> fin_cases i <;> decide +kernel)

theorem inside (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 10) (P : ℚ × ℚ)
    (hp : P ∈ queryInsidePoints (masks b i) 2 (owned i)) :
    (owner b p i).Inside P.1 P.2 := by
  have aux : AuxExact (owner b p i) 2 (owned i) := by
    simpa only [owner,forced b p hf i] using nat_combined_exact p (ownerIndex p (masks b i))
  exact query_inside_sound _ 2 _ _
    (by change 1 < (p.square _).side; rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square _).side ≤ 1001/1000; rw [p.congruent]; exact p.side_le)
    (p.contained _) (by simpa only [owner,owner_code b p hf i] using
      coded_exact p (ownerIndex p (masks b i))) aux P hp

theorem outside (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i : Fin 10) (P : ℚ × ℚ)
    (hp : P ∈ queryOutsidePoints (masks b i) 2 (owned i)) :
    ¬ (owner b p i).Inside P.1 P.2 := by
  have aux : AuxExact (owner b p i) 2 (owned i) := by
    simpa only [owner,forced b p hf i] using nat_combined_exact p (ownerIndex p (masks b i))
  exact query_outside_sound _ 2 _ _
    (by simpa only [owner,owner_code b p hf i] using
      coded_exact p (ownerIndex p (masks b i))) aux P hp

theorem apart (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family b) (i j : Fin 10) (hne : i ≠ j) :
    ∀ x y, ¬ ((owner b p i).Inside x y ∧ (owner b p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have injective : Function.Injective (masks b) := by cases b <;> decide +kernel
  exact hne (injective ((owner_code b p hf i).symm.trans
    ((congrArg (markerCode p) equal).trans (owner_code b p hf j))))

#print axioms forced
end N12Compact.C849851

import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 842, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareUnusedCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family842 : Finset Nat := {1,2,12,16,192,256,512,1024,2048,4096,8192,16416}

def domain842_1 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain842_2 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain842_16 : CertifiedDomain family842 :=
  OwnerBudget.product family842 16
    (HalfDomain.ofSpec family842 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family842 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain842_256 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain842_512 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain842_1024 : CertifiedDomain family842 :=
  OwnerBudget.product family842 1024
    (HalfDomain.ofSpec family842 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family842 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain842_2048 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain842_4096 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain842_8192 : CertifiedDomain family842 :=
  CertifiedDomain.ofCombined family842 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain842_16416 : CertifiedDomain family842 :=
  OwnerBudget.product family842 16416
    (HalfDomain.ofSpec family842 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family842 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domains842 : List (CertifiedDomain family842) :=
  [domain842_1,domain842_2,domain842_16,domain842_16416,domain842_4096,domain842_8192,domain842_256,domain842_512,domain842_1024,domain842_2048]

theorem domains842_members : ∀ d ∈ domains842, d.mask ∈ family842 := by decide +kernel
theorem domains842_distinct : domains842.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data842 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16416,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[⟨(3,9/4),(3,11/4),(3,9/4),(3,12/5),3/10,0⟩],[]]⟩

theorem data842_checked : data842.Check family842 := by decide +kernel

theorem forced842 (p : NormalizedPacking) (hf : codedMarkerFamily p = family842) :
    ∀ i, natCombinedOwners p (ownerIndex p (data842.masks i)) = data842.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains842 domains842_members domains842_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains842 domains842_members domains842_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains842 domains842_members domains842_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains842 domains842_members domains842_distinct
      16416 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains842 domains842_members domains842_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case842_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family842) : False :=
  FourSquareConvexCase.impossible data842 family842 data842_checked forced842 p hf

#print axioms case842_impossible
end
end N12Compact.FourSquareUnusedCases

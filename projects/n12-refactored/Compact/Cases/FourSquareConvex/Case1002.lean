import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 1002, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1002 : Finset Nat := {1,2,12,192,256,512,1024,2048,4096,8192,16416,32784}

def domain1002_1 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1002_2 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain1002_256 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1002_512 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1002_1024 : CertifiedDomain family1002 :=
  OwnerBudget.product family1002 1024
    (HalfDomain.ofSpec family1002 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1002 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1002_2048 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1002_4096 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain1002_8192 : CertifiedDomain family1002 :=
  CertifiedDomain.ofCombined family1002 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1002_16416 : CertifiedDomain family1002 :=
  OwnerBudget.product family1002 16416
    (HalfDomain.ofSpec family1002 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family1002 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain1002_32784 : CertifiedDomain family1002 :=
  OwnerBudget.product family1002 32784
    (HalfDomain.ofSeedHull family1002 32784 0 7 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,3),(11/4,3),(9/4,3),(12/5,3),3/10,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSpec family1002 singleSpec92 1 singleSpec92_checked (by decide +kernel))

def domains1002 : List (CertifiedDomain family1002) :=
  [domain1002_1,domain1002_2,domain1002_16416,domain1002_32784,domain1002_4096,domain1002_8192,domain1002_256,domain1002_512,domain1002_1024,domain1002_2048]

theorem domains1002_members : ∀ d ∈ domains1002, d.mask ∈ family1002 := by decide +kernel
theorem domains1002_distinct : domains1002.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1002 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16416,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[⟨(3,9/4),(3,11/4),(3,9/4),(3,12/5),3/10,0⟩],[]]⟩

theorem data1002_checked : data1002.Check family1002 := by decide +kernel

theorem forced1002 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1002) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1002.masks i)) = data1002.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1002 domains1002_members domains1002_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains1002 domains1002_members domains1002_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains1002 domains1002_members domains1002_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains1002 domains1002_members domains1002_distinct
      16416 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains1002 domains1002_members domains1002_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case1002_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1002) : False :=
  FourSquareConvexCase.impossible data1002 family1002 data1002_checked forced1002 p hf

#print axioms case1002_impossible
end
end N12Compact.FourSquareConvexCases

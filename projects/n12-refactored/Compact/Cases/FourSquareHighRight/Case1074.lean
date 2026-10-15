import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1074. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1074 : Finset Nat := {1,12,16,192,256,512,1024,2048,4098,8192,16416,32768}

def domain1074_1 : CertifiedDomain family1074 :=
  CertifiedDomain.ofCombined family1074 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1074_16 : CertifiedDomain family1074 :=
  OwnerBudget.product family1074 16
    (HalfDomain.ofSpec family1074 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family1074 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain1074_256 : CertifiedDomain family1074 :=
  CertifiedDomain.ofCombined family1074 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1074_512 : CertifiedDomain family1074 :=
  CertifiedDomain.ofCombined family1074 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1074_1024 : CertifiedDomain family1074 :=
  OwnerBudget.product family1074 1024
    (HalfDomain.ofSpec family1074 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1074 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1074_2048 : CertifiedDomain family1074 :=
  CertifiedDomain.ofCombined family1074 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1074_4098 : CertifiedDomain family1074 :=
  OwnerBudget.product family1074 4098
    (HalfDomain.ofSpec family1074 singleSpec59 0 singleSpec59_checked (by decide +kernel))
    (HalfDomain.singleton family1074 4098 1 (by decide +kernel) (by decide +kernel))

def domain1074_8192 : CertifiedDomain family1074 :=
  CertifiedDomain.ofCombined family1074 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1074_16416 : CertifiedDomain family1074 :=
  OwnerBudget.product family1074 16416
    (HalfDomain.ofSpec family1074 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family1074 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain1074_32768 : CertifiedDomain family1074 :=
  CertifiedDomain.ofCombined family1074 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1074 : List (CertifiedDomain family1074) :=
  [domain1074_1,domain1074_16,domain1074_16416,domain1074_8192,domain1074_32768,domain1074_256,domain1074_512,domain1074_1024,domain1074_2048,domain1074_4098]

theorem domains1074_members : ∀ d ∈ domains1074, d.mask ∈ family1074 := by decide +kernel
theorem domains1074_distinct : domains1074.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1074 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data1074_checked : data1074.Check family1074 := by decide +kernel

theorem forced1074 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1074) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1074.masks i)) = data1074.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1074 domains1074_members domains1074_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains1074 domains1074_members domains1074_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains1074 domains1074_members domains1074_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains1074 domains1074_members domains1074_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case1074_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1074) : False :=
  FourSquareCaseHighRight.impossible data1074 family1074 data1074_checked forced1074 p hf

#print axioms case1074_impossible
end N12Compact.FourSquareHighRightCases

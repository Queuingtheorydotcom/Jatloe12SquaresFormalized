import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1073. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1073 : Finset Nat := {1,12,16,192,256,512,1024,2048,4096,8192,16416,32768}

def domain1073_1 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1073_16 : CertifiedDomain family1073 :=
  OwnerBudget.product family1073 16
    (HalfDomain.ofSpec family1073 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family1073 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain1073_256 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1073_512 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1073_1024 : CertifiedDomain family1073 :=
  OwnerBudget.product family1073 1024
    (HalfDomain.ofSpec family1073 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1073 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1073_2048 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1073_4096 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain1073_8192 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1073_16416 : CertifiedDomain family1073 :=
  OwnerBudget.product family1073 16416
    (HalfDomain.ofSpec family1073 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family1073 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain1073_32768 : CertifiedDomain family1073 :=
  CertifiedDomain.ofCombined family1073 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1073 : List (CertifiedDomain family1073) :=
  [domain1073_1,domain1073_16,domain1073_16416,domain1073_4096,domain1073_8192,domain1073_32768,domain1073_256,domain1073_512,domain1073_1024,domain1073_2048]

theorem domains1073_members : ∀ d ∈ domains1073, d.mask ∈ family1073 := by decide +kernel
theorem domains1073_distinct : domains1073.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1073 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data1073_checked : data1073.Check family1073 := by decide +kernel

theorem forced1073 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1073) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1073.masks i)) = data1073.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1073 domains1073_members domains1073_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains1073 domains1073_members domains1073_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains1073 domains1073_members domains1073_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains1073 domains1073_members domains1073_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case1073_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1073) : False :=
  FourSquareCaseHighRight.impossible data1073 family1073 data1073_checked forced1073 p hf

#print axioms case1073_impossible
end N12Compact.FourSquareHighRightCases

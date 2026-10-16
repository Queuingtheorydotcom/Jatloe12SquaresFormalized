import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 886. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family886 : Finset Nat := {1,2,12,16,192,512,1024,2048,4352,8192,16384,32768}

def domain886_1 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain886_2 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain886_16 : CertifiedDomain family886 :=
  OwnerBudget.product family886 16
    (HalfDomain.ofSpec family886 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family886 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain886_512 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain886_1024 : CertifiedDomain family886 :=
  OwnerBudget.product family886 1024
    (HalfDomain.ofSpec family886 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family886 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain886_2048 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain886_4352 : CertifiedDomain family886 :=
  OwnerBudget.product family886 4352
    (HalfDomain.ofSpec family886 singleSpec64 0 singleSpec64_checked (by decide +kernel))
    (HalfDomain.singleton family886 4352 1 (by decide +kernel) (by decide +kernel))

def domain886_8192 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain886_16384 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain886_32768 : CertifiedDomain family886 :=
  CertifiedDomain.ofCombined family886 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains886 : List (CertifiedDomain family886) :=
  [domain886_1,domain886_2,domain886_16,domain886_8192,domain886_16384,domain886_32768,domain886_512,domain886_1024,domain886_2048,domain886_4352]

theorem domains886_members : ∀ d ∈ domains886, d.mask ∈ family886 := by decide +kernel
theorem domains886_distinct : domains886.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data886 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data886_checked : data886.Check family886 := by decide +kernel

theorem forced886 (p : NormalizedPacking) (hf : codedMarkerFamily p = family886) :
    ∀ i, natCombinedOwners p (ownerIndex p (data886.masks i)) = data886.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains886 domains886_members domains886_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains886 domains886_members domains886_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains886 domains886_members domains886_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains886 domains886_members domains886_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case886_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family886) : False :=
  FourSquareCaseHighRight.impossible data886 family886 data886_checked forced886 p hf

#print axioms case886_impossible
end N12Compact.FourSquareHighRightCases

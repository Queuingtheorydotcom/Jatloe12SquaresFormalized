import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 670. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family670 : Finset Nat := {1,2,12,16,32,192,256,512,1024,2048,4096,16384}

def domain670_1 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain670_2 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain670_16 : CertifiedDomain family670 :=
  OwnerBudget.product family670 16
    (HalfDomain.ofSpec family670 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family670 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain670_32 : CertifiedDomain family670 :=
  OwnerBudget.product family670 32
    (HalfDomain.ofSpec family670 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family670 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain670_256 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain670_512 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain670_1024 : CertifiedDomain family670 :=
  OwnerBudget.product family670 1024
    (HalfDomain.ofSpec family670 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family670 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain670_2048 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain670_4096 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain670_16384 : CertifiedDomain family670 :=
  CertifiedDomain.ofCombined family670 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domains670 : List (CertifiedDomain family670) :=
  [domain670_1,domain670_2,domain670_16,domain670_32,domain670_4096,domain670_16384,domain670_256,domain670_512,domain670_1024,domain670_2048]

theorem domains670_members : ∀ d ∈ domains670, d.mask ∈ family670 := by decide +kernel
theorem domains670_distinct : domains670.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data670 : FourSquareCaseHighRight.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,32],
    ![{5,16},{3,14},{1,11},{9,19}], 2⟩

theorem data670_checked : data670.Check family670 := by decide +kernel

theorem forced670 (p : NormalizedPacking) (hf : codedMarkerFamily p = family670) :
    ∀ i, natCombinedOwners p (ownerIndex p (data670.masks i)) = data670.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains670 domains670_members domains670_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains670 domains670_members domains670_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains670 domains670_members domains670_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains670 domains670_members domains670_distinct
      32 {9,19} (by decide +kernel) p hf

theorem case670_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family670) : False :=
  FourSquareCaseHighRight.impossible data670 family670 data670_checked forced670 p hf

#print axioms case670_impossible
end N12Compact.FourSquareHighRightExtraCases

import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 674. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family674 : Finset Nat := {1,2,12,16,32,192,256,512,1024,4096,8192,34816}

def domain674_1 : CertifiedDomain family674 :=
  CertifiedDomain.ofCombined family674 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain674_2 : CertifiedDomain family674 :=
  CertifiedDomain.ofCombined family674 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain674_16 : CertifiedDomain family674 :=
  OwnerBudget.product family674 16
    (HalfDomain.ofSpec family674 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family674 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain674_32 : CertifiedDomain family674 :=
  OwnerBudget.product family674 32
    (HalfDomain.ofSpec family674 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family674 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain674_256 : CertifiedDomain family674 :=
  CertifiedDomain.ofCombined family674 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain674_512 : CertifiedDomain family674 :=
  CertifiedDomain.ofCombined family674 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain674_1024 : CertifiedDomain family674 :=
  OwnerBudget.product family674 1024
    (HalfDomain.ofSpec family674 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family674 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain674_4096 : CertifiedDomain family674 :=
  CertifiedDomain.ofCombined family674 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain674_8192 : CertifiedDomain family674 :=
  CertifiedDomain.ofCombined family674 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain674_34816 : CertifiedDomain family674 :=
  OwnerBudget.product family674 34816
    (HalfDomain.singleton family674 34816 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.singleton family674 34816 1 (by decide +kernel) (by decide +kernel))

def domains674 : List (CertifiedDomain family674) :=
  [domain674_1,domain674_2,domain674_16,domain674_32,domain674_4096,domain674_8192,domain674_256,domain674_512,domain674_1024,domain674_34816]

theorem domains674_members : ∀ d ∈ domains674, d.mask ∈ family674 := by decide +kernel
theorem domains674_distinct : domains674.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data674 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data674_checked : data674.Check family674 := by decide +kernel

theorem forced674 (p : NormalizedPacking) (hf : codedMarkerFamily p = family674) :
    ∀ i, natCombinedOwners p (ownerIndex p (data674.masks i)) = data674.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains674 domains674_members domains674_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains674 domains674_members domains674_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains674 domains674_members domains674_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains674 domains674_members domains674_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case674_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family674) : False :=
  FourSquareCaseHighRight.impossible data674 family674 data674_checked forced674 p hf

#print axioms case674_impossible
end N12Compact.FourSquareHighRightExtraCases

import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 675. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family675 : Finset Nat := {1,2,12,16,32,192,256,512,1024,4096,16384,34816}

def domain675_1 : CertifiedDomain family675 :=
  CertifiedDomain.ofCombined family675 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain675_2 : CertifiedDomain family675 :=
  CertifiedDomain.ofCombined family675 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain675_16 : CertifiedDomain family675 :=
  OwnerBudget.product family675 16
    (HalfDomain.ofSpec family675 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family675 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain675_32 : CertifiedDomain family675 :=
  OwnerBudget.product family675 32
    (HalfDomain.ofSpec family675 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family675 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain675_256 : CertifiedDomain family675 :=
  CertifiedDomain.ofCombined family675 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain675_512 : CertifiedDomain family675 :=
  CertifiedDomain.ofCombined family675 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain675_1024 : CertifiedDomain family675 :=
  OwnerBudget.product family675 1024
    (HalfDomain.ofSpec family675 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family675 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain675_4096 : CertifiedDomain family675 :=
  CertifiedDomain.ofCombined family675 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain675_16384 : CertifiedDomain family675 :=
  CertifiedDomain.ofCombined family675 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain675_34816 : CertifiedDomain family675 :=
  OwnerBudget.product family675 34816
    (HalfDomain.singleton family675 34816 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.singleton family675 34816 1 (by decide +kernel) (by decide +kernel))

def domains675 : List (CertifiedDomain family675) :=
  [domain675_1,domain675_2,domain675_16,domain675_32,domain675_4096,domain675_16384,domain675_256,domain675_512,domain675_1024,domain675_34816]

theorem domains675_members : ∀ d ∈ domains675, d.mask ∈ family675 := by decide +kernel
theorem domains675_distinct : domains675.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data675 : FourSquareCaseHighRight.Data :=
  ⟨⟨false,true,true⟩, ![256,512,16384,2],
    ![{4,13},{6,15},{8,18},{0,10}], 32⟩

theorem data675_checked : data675.Check family675 := by decide +kernel

theorem forced675 (p : NormalizedPacking) (hf : codedMarkerFamily p = family675) :
    ∀ i, natCombinedOwners p (ownerIndex p (data675.masks i)) = data675.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains675 domains675_members domains675_distinct
      256 {4,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains675 domains675_members domains675_distinct
      512 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains675 domains675_members domains675_distinct
      16384 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains675 domains675_members domains675_distinct
      2 {0,10} (by decide +kernel) p hf

theorem case675_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family675) : False :=
  FourSquareCaseHighRight.impossible data675 family675 data675_checked forced675 p hf

#print axioms case675_impossible
end N12Compact.FourSquareHighRightExtraCases

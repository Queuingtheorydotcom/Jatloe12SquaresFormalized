import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 673. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family673 : Finset Nat := {1,2,12,16,32,192,256,512,1024,4096,8192,32768}

def domain673_1 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain673_2 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain673_16 : CertifiedDomain family673 :=
  OwnerBudget.product family673 16
    (HalfDomain.ofSpec family673 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family673 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain673_32 : CertifiedDomain family673 :=
  OwnerBudget.product family673 32
    (HalfDomain.ofSpec family673 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family673 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain673_256 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain673_512 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain673_1024 : CertifiedDomain family673 :=
  OwnerBudget.product family673 1024
    (HalfDomain.ofSpec family673 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family673 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain673_4096 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain673_8192 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain673_32768 : CertifiedDomain family673 :=
  CertifiedDomain.ofCombined family673 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains673 : List (CertifiedDomain family673) :=
  [domain673_1,domain673_2,domain673_16,domain673_32,domain673_4096,domain673_8192,domain673_32768,domain673_256,domain673_512,domain673_1024]

theorem domains673_members : ∀ d ∈ domains673, d.mask ∈ family673 := by decide +kernel
theorem domains673_distinct : domains673.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data673 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data673_checked : data673.Check family673 := by decide +kernel

theorem forced673 (p : NormalizedPacking) (hf : codedMarkerFamily p = family673) :
    ∀ i, natCombinedOwners p (ownerIndex p (data673.masks i)) = data673.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains673 domains673_members domains673_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains673 domains673_members domains673_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains673 domains673_members domains673_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains673 domains673_members domains673_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case673_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family673) : False :=
  FourSquareCaseHighRight.impossible data673 family673 data673_checked forced673 p hf

#print axioms case673_impossible
end N12Compact.FourSquareHighRightExtraCases

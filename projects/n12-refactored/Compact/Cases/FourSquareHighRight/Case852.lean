import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 852. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family852 : Finset Nat := {1,2,12,16,192,256,512,1024,6144,8192,16384,32768}

def domain852_1 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain852_2 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain852_16 : CertifiedDomain family852 :=
  OwnerBudget.product family852 16
    (HalfDomain.ofSpec family852 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family852 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain852_256 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain852_512 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain852_1024 : CertifiedDomain family852 :=
  OwnerBudget.product family852 1024
    (HalfDomain.ofSpec family852 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family852 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain852_6144 : CertifiedDomain family852 :=
  OwnerBudget.product family852 6144
    (HalfDomain.singleton family852 6144 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.singleton family852 6144 1 (by decide +kernel) (by decide +kernel))

def domain852_8192 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain852_16384 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain852_32768 : CertifiedDomain family852 :=
  CertifiedDomain.ofCombined family852 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains852 : List (CertifiedDomain family852) :=
  [domain852_1,domain852_2,domain852_16,domain852_8192,domain852_16384,domain852_32768,domain852_256,domain852_512,domain852_1024,domain852_6144]

theorem domains852_members : ∀ d ∈ domains852, d.mask ∈ family852 := by decide +kernel
theorem domains852_distinct : domains852.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data852 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data852_checked : data852.Check family852 := by decide +kernel

theorem forced852 (p : NormalizedPacking) (hf : codedMarkerFamily p = family852) :
    ∀ i, natCombinedOwners p (ownerIndex p (data852.masks i)) = data852.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains852 domains852_members domains852_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains852 domains852_members domains852_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains852 domains852_members domains852_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains852 domains852_members domains852_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case852_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family852) : False :=
  FourSquareCaseHighRight.impossible data852 family852 data852_checked forced852 p hf

#print axioms case852_impossible
end N12Compact.FourSquareHighRightCases

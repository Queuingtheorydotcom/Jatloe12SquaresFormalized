import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 846. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family846 : Finset Nat := {1,2,12,16,192,256,512,1024,2048,8192,16384,32768}

def domain846_1 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain846_2 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain846_16 : CertifiedDomain family846 :=
  OwnerBudget.product family846 16
    (HalfDomain.ofSpec family846 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family846 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain846_256 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain846_512 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain846_1024 : CertifiedDomain family846 :=
  OwnerBudget.product family846 1024
    (HalfDomain.ofSpec family846 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family846 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain846_2048 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain846_8192 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain846_16384 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain846_32768 : CertifiedDomain family846 :=
  CertifiedDomain.ofCombined family846 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains846 : List (CertifiedDomain family846) :=
  [domain846_1,domain846_2,domain846_16,domain846_8192,domain846_16384,domain846_32768,domain846_256,domain846_512,domain846_1024,domain846_2048]

theorem domains846_members : ∀ d ∈ domains846, d.mask ∈ family846 := by decide +kernel
theorem domains846_distinct : domains846.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data846 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data846_checked : data846.Check family846 := by decide +kernel

theorem forced846 (p : NormalizedPacking) (hf : codedMarkerFamily p = family846) :
    ∀ i, natCombinedOwners p (ownerIndex p (data846.masks i)) = data846.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains846 domains846_members domains846_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains846 domains846_members domains846_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains846 domains846_members domains846_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains846 domains846_members domains846_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case846_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family846) : False :=
  FourSquareCaseHighRight.impossible data846 family846 data846_checked forced846 p hf

#print axioms case846_impossible
end N12Compact.FourSquareHighRightCases

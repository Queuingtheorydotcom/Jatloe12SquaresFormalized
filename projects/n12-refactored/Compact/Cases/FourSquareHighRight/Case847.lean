import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 847. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family847 : Finset Nat := {1,2,12,16,192,256,512,1024,2048,8192,16416,32768}

def domain847_1 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain847_2 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain847_16 : CertifiedDomain family847 :=
  OwnerBudget.product family847 16
    (HalfDomain.ofSpec family847 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family847 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain847_256 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain847_512 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain847_1024 : CertifiedDomain family847 :=
  OwnerBudget.product family847 1024
    (HalfDomain.ofSpec family847 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family847 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain847_2048 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain847_8192 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain847_16416 : CertifiedDomain family847 :=
  OwnerBudget.product family847 16416
    (HalfDomain.ofSpec family847 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family847 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain847_32768 : CertifiedDomain family847 :=
  CertifiedDomain.ofCombined family847 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains847 : List (CertifiedDomain family847) :=
  [domain847_1,domain847_2,domain847_16,domain847_16416,domain847_8192,domain847_32768,domain847_256,domain847_512,domain847_1024,domain847_2048]

theorem domains847_members : ∀ d ∈ domains847, d.mask ∈ family847 := by decide +kernel
theorem domains847_distinct : domains847.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data847 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data847_checked : data847.Check family847 := by decide +kernel

theorem forced847 (p : NormalizedPacking) (hf : codedMarkerFamily p = family847) :
    ∀ i, natCombinedOwners p (ownerIndex p (data847.masks i)) = data847.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains847 domains847_members domains847_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains847 domains847_members domains847_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains847 domains847_members domains847_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains847 domains847_members domains847_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case847_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family847) : False :=
  FourSquareCaseHighRight.impossible data847 family847 data847_checked forced847 p hf

#print axioms case847_impossible
end N12Compact.FourSquareHighRightCases

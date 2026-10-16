import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 887. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family887 : Finset Nat := {1,2,12,16,192,512,1024,2048,4352,8192,16416,32768}

def domain887_1 : CertifiedDomain family887 :=
  CertifiedDomain.ofCombined family887 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain887_2 : CertifiedDomain family887 :=
  CertifiedDomain.ofCombined family887 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain887_16 : CertifiedDomain family887 :=
  OwnerBudget.product family887 16
    (HalfDomain.ofSpec family887 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family887 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain887_512 : CertifiedDomain family887 :=
  CertifiedDomain.ofCombined family887 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain887_1024 : CertifiedDomain family887 :=
  OwnerBudget.product family887 1024
    (HalfDomain.ofSpec family887 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family887 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain887_2048 : CertifiedDomain family887 :=
  CertifiedDomain.ofCombined family887 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain887_4352 : CertifiedDomain family887 :=
  OwnerBudget.product family887 4352
    (HalfDomain.ofSpec family887 singleSpec64 0 singleSpec64_checked (by decide +kernel))
    (HalfDomain.singleton family887 4352 1 (by decide +kernel) (by decide +kernel))

def domain887_8192 : CertifiedDomain family887 :=
  CertifiedDomain.ofCombined family887 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain887_16416 : CertifiedDomain family887 :=
  OwnerBudget.product family887 16416
    (HalfDomain.ofSpec family887 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family887 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain887_32768 : CertifiedDomain family887 :=
  CertifiedDomain.ofCombined family887 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains887 : List (CertifiedDomain family887) :=
  [domain887_1,domain887_2,domain887_16,domain887_16416,domain887_8192,domain887_32768,domain887_512,domain887_1024,domain887_2048,domain887_4352]

theorem domains887_members : ∀ d ∈ domains887, d.mask ∈ family887 := by decide +kernel
theorem domains887_distinct : domains887.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data887 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data887_checked : data887.Check family887 := by decide +kernel

theorem forced887 (p : NormalizedPacking) (hf : codedMarkerFamily p = family887) :
    ∀ i, natCombinedOwners p (ownerIndex p (data887.masks i)) = data887.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains887 domains887_members domains887_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains887 domains887_members domains887_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains887 domains887_members domains887_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains887 domains887_members domains887_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case887_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family887) : False :=
  FourSquareCaseHighRight.impossible data887 family887 data887_checked forced887 p hf

#print axioms case887_impossible
end N12Compact.FourSquareHighRightCases

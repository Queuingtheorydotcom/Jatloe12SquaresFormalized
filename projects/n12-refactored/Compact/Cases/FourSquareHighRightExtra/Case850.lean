import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 850. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family850 : Finset Nat := {1,2,12,16,192,256,512,1024,4096,8192,16416,32768}

def domain850_1 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain850_2 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain850_16 : CertifiedDomain family850 :=
  OwnerBudget.product family850 16
    (HalfDomain.ofSpec family850 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family850 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain850_256 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain850_512 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain850_1024 : CertifiedDomain family850 :=
  OwnerBudget.product family850 1024
    (HalfDomain.ofSpec family850 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family850 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain850_4096 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain850_8192 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain850_16416 : CertifiedDomain family850 :=
  OwnerBudget.product family850 16416
    (HalfDomain.ofSpec family850 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family850 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain850_32768 : CertifiedDomain family850 :=
  CertifiedDomain.ofCombined family850 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains850 : List (CertifiedDomain family850) :=
  [domain850_1,domain850_2,domain850_16,domain850_16416,domain850_4096,domain850_8192,domain850_32768,domain850_256,domain850_512,domain850_1024]

theorem domains850_members : ∀ d ∈ domains850, d.mask ∈ family850 := by decide +kernel
theorem domains850_distinct : domains850.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data850 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data850_checked : data850.Check family850 := by decide +kernel

theorem forced850 (p : NormalizedPacking) (hf : codedMarkerFamily p = family850) :
    ∀ i, natCombinedOwners p (ownerIndex p (data850.masks i)) = data850.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains850 domains850_members domains850_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains850 domains850_members domains850_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains850 domains850_members domains850_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains850 domains850_members domains850_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case850_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family850) : False :=
  FourSquareCaseHighRight.impossible data850 family850 data850_checked forced850 p hf

#print axioms case850_impossible
end N12Compact.FourSquareHighRightExtraCases

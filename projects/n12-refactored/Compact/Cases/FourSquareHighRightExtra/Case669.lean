import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 669. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family669 : Finset Nat := {1,2,12,16,32,192,256,512,1024,2048,4096,8192}

def domain669_1 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain669_2 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain669_16 : CertifiedDomain family669 :=
  OwnerBudget.product family669 16
    (HalfDomain.ofSpec family669 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family669 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain669_32 : CertifiedDomain family669 :=
  OwnerBudget.product family669 32
    (HalfDomain.ofSpec family669 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family669 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain669_256 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain669_512 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain669_1024 : CertifiedDomain family669 :=
  OwnerBudget.product family669 1024
    (HalfDomain.ofSpec family669 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family669 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain669_2048 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain669_4096 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain669_8192 : CertifiedDomain family669 :=
  CertifiedDomain.ofCombined family669 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domains669 : List (CertifiedDomain family669) :=
  [domain669_1,domain669_2,domain669_16,domain669_32,domain669_4096,domain669_8192,domain669_256,domain669_512,domain669_1024,domain669_2048]

theorem domains669_members : ∀ d ∈ domains669, d.mask ∈ family669 := by decide +kernel
theorem domains669_distinct : domains669.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data669 : FourSquareCaseHighRight.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,32],
    ![{5,16},{3,14},{1,11},{9,19}], 2⟩

theorem data669_checked : data669.Check family669 := by decide +kernel

theorem forced669 (p : NormalizedPacking) (hf : codedMarkerFamily p = family669) :
    ∀ i, natCombinedOwners p (ownerIndex p (data669.masks i)) = data669.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains669 domains669_members domains669_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains669 domains669_members domains669_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains669 domains669_members domains669_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains669 domains669_members domains669_distinct
      32 {9,19} (by decide +kernel) p hf

theorem case669_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family669) : False :=
  FourSquareCaseHighRight.impossible data669 family669 data669_checked forced669 p hf

#print axioms case669_impossible
end N12Compact.FourSquareHighRightExtraCases

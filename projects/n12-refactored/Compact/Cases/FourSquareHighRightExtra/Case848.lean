import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 848. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightExtraCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family848 : Finset Nat := {1,2,12,16,192,256,512,1024,4096,8192,16384,32768}

def domain848_1 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain848_2 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain848_16 : CertifiedDomain family848 :=
  OwnerBudget.product family848 16
    (HalfDomain.ofSpec family848 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family848 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain848_256 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain848_512 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain848_1024 : CertifiedDomain family848 :=
  OwnerBudget.product family848 1024
    (HalfDomain.ofSpec family848 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family848 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain848_4096 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain848_8192 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain848_16384 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain848_32768 : CertifiedDomain family848 :=
  CertifiedDomain.ofCombined family848 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains848 : List (CertifiedDomain family848) :=
  [domain848_1,domain848_2,domain848_16,domain848_4096,domain848_8192,domain848_16384,domain848_32768,domain848_256,domain848_512,domain848_1024]

theorem domains848_members : ∀ d ∈ domains848, d.mask ∈ family848 := by decide +kernel
theorem domains848_distinct : domains848.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data848 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data848_checked : data848.Check family848 := by decide +kernel

theorem forced848 (p : NormalizedPacking) (hf : codedMarkerFamily p = family848) :
    ∀ i, natCombinedOwners p (ownerIndex p (data848.masks i)) = data848.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains848 domains848_members domains848_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains848 domains848_members domains848_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains848 domains848_members domains848_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains848 domains848_members domains848_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case848_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family848) : False :=
  FourSquareCaseHighRight.impossible data848 family848 data848_checked forced848 p hf

#print axioms case848_impossible
end N12Compact.FourSquareHighRightExtraCases

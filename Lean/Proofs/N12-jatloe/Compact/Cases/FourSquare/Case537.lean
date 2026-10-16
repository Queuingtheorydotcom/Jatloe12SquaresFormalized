import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 537: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family537 : Finset Nat := {1,2,8,48,192,256,512,1024,2048,4096,16384,32768}

def domain537_1 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain537_2 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain537_8 : CertifiedDomain family537 :=
  OwnerBudget.product family537 8
    (HalfDomain.ofSpec family537 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family537 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain537_256 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain537_512 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain537_1024 : CertifiedDomain family537 :=
  OwnerBudget.product family537 1024
    (HalfDomain.ofSpec family537 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family537 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain537_2048 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain537_4096 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain537_16384 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain537_32768 : CertifiedDomain family537 :=
  CertifiedDomain.ofCombined family537 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains537 : List (CertifiedDomain family537) :=
  [domain537_1,domain537_2,domain537_8,domain537_4096,domain537_16384,domain537_32768,domain537_256,domain537_512,domain537_1024,domain537_2048]

theorem domains537_members : ∀ d ∈ domains537, d.mask ∈ family537 := by decide +kernel
theorem domains537_distinct : domains537.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data537 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data537_checked : (data537).Check family537 := by decide +kernel

theorem forced537 (p : NormalizedPacking) (hf : codedMarkerFamily p = family537) :
    ∀ i, natCombinedOwners p (ownerIndex p (data537.masks i)) = data537.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains537 domains537_members domains537_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains537 domains537_members domains537_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains537 domains537_members domains537_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains537 domains537_members domains537_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case537_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family537) : False :=
  FourSquareCase.impossible data537 family537 data537_checked forced537 p hf

#print axioms case537_impossible
end N12Compact.FourSquareCases

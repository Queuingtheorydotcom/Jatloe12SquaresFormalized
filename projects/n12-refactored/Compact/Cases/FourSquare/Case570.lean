import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 570: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family570 : Finset Nat := {1,2,8,48,192,256,1024,2048,4096,8708,16384,32768}

def domain570_1 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain570_2 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain570_8 : CertifiedDomain family570 :=
  OwnerBudget.product family570 8
    (HalfDomain.ofSpec family570 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family570 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain570_256 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain570_1024 : CertifiedDomain family570 :=
  OwnerBudget.product family570 1024
    (HalfDomain.ofSpec family570 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family570 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain570_2048 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain570_4096 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain570_8708 : CertifiedDomain family570 :=
  OwnerBudget.product family570 8708
    (HalfDomain.singleton family570 8708 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSeedHull family570 8708 1 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain570_16384 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain570_32768 : CertifiedDomain family570 :=
  CertifiedDomain.ofCombined family570 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains570 : List (CertifiedDomain family570) :=
  [domain570_1,domain570_2,domain570_8,domain570_4096,domain570_16384,domain570_32768,domain570_256,domain570_1024,domain570_2048,domain570_8708]

theorem domains570_members : ∀ d ∈ domains570, d.mask ∈ family570 := by decide +kernel
theorem domains570_distinct : domains570.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data570 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data570_checked : (data570).Check family570 := by decide +kernel

theorem forced570 (p : NormalizedPacking) (hf : codedMarkerFamily p = family570) :
    ∀ i, natCombinedOwners p (ownerIndex p (data570.masks i)) = data570.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains570 domains570_members domains570_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains570 domains570_members domains570_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains570 domains570_members domains570_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains570 domains570_members domains570_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case570_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family570) : False :=
  FourSquareCase.impossible data570 family570 data570_checked forced570 p hf

#print axioms case570_impossible
end N12Compact.FourSquareCases

import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 569: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family569 : Finset Nat := {1,2,8,48,192,256,1024,2048,4096,8704,16384,32768}

def domain569_1 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain569_2 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain569_8 : CertifiedDomain family569 :=
  OwnerBudget.product family569 8
    (HalfDomain.ofSpec family569 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family569 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain569_256 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain569_1024 : CertifiedDomain family569 :=
  OwnerBudget.product family569 1024
    (HalfDomain.ofSpec family569 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family569 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain569_2048 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain569_4096 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain569_8704 : CertifiedDomain family569 :=
  OwnerBudget.product family569 8704
    (HalfDomain.ofSpec family569 singleSpec74 0 singleSpec74_checked (by decide +kernel))
    (HalfDomain.singleton family569 8704 1 (by decide +kernel) (by decide +kernel))

def domain569_16384 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain569_32768 : CertifiedDomain family569 :=
  CertifiedDomain.ofCombined family569 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains569 : List (CertifiedDomain family569) :=
  [domain569_1,domain569_2,domain569_8,domain569_4096,domain569_16384,domain569_32768,domain569_256,domain569_1024,domain569_2048,domain569_8704]

theorem domains569_members : ∀ d ∈ domains569, d.mask ∈ family569 := by decide +kernel
theorem domains569_distinct : domains569.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data569 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data569_checked : (data569).Check family569 := by decide +kernel

theorem forced569 (p : NormalizedPacking) (hf : codedMarkerFamily p = family569) :
    ∀ i, natCombinedOwners p (ownerIndex p (data569.masks i)) = data569.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains569 domains569_members domains569_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains569 domains569_members domains569_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains569 domains569_members domains569_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains569 domains569_members domains569_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case569_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family569) : False :=
  FourSquareCase.impossible data569 family569 data569_checked forced569 p hf

#print axioms case569_impossible
end N12Compact.FourSquareCases

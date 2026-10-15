import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 585: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family585 : Finset Nat := {1,2,8,48,192,516,1024,2048,4096,8448,16384,32768}

def domain585_1 : CertifiedDomain family585 :=
  CertifiedDomain.ofCombined family585 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain585_2 : CertifiedDomain family585 :=
  CertifiedDomain.ofCombined family585 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain585_8 : CertifiedDomain family585 :=
  OwnerBudget.product family585 8
    (HalfDomain.ofSpec family585 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family585 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain585_516 : CertifiedDomain family585 :=
  OwnerBudget.product family585 516
    (HalfDomain.ofSpec family585 singleSpec29 0 singleSpec29_checked (by decide +kernel))
    (HalfDomain.ofSpec family585 singleSpec30 1 singleSpec30_checked (by decide +kernel))

def domain585_1024 : CertifiedDomain family585 :=
  OwnerBudget.product family585 1024
    (HalfDomain.ofSpec family585 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family585 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain585_2048 : CertifiedDomain family585 :=
  CertifiedDomain.ofCombined family585 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain585_4096 : CertifiedDomain family585 :=
  CertifiedDomain.ofCombined family585 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain585_8448 : CertifiedDomain family585 :=
  OwnerBudget.product family585 8448
    (HalfDomain.ofSpec family585 singleSpec72 0 singleSpec72_checked (by decide +kernel))
    (HalfDomain.ofSpec family585 singleSpec73 1 singleSpec73_checked (by decide +kernel))

def domain585_16384 : CertifiedDomain family585 :=
  CertifiedDomain.ofCombined family585 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain585_32768 : CertifiedDomain family585 :=
  CertifiedDomain.ofCombined family585 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains585 : List (CertifiedDomain family585) :=
  [domain585_1,domain585_2,domain585_8,domain585_4096,domain585_16384,domain585_32768,domain585_516,domain585_1024,domain585_2048,domain585_8448]

theorem domains585_members : ∀ d ∈ domains585, d.mask ∈ family585 := by decide +kernel
theorem domains585_distinct : domains585.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data585 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data585_checked : (data585).Check family585 := by decide +kernel

theorem forced585 (p : NormalizedPacking) (hf : codedMarkerFamily p = family585) :
    ∀ i, natCombinedOwners p (ownerIndex p (data585.masks i)) = data585.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains585 domains585_members domains585_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains585 domains585_members domains585_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains585 domains585_members domains585_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains585 domains585_members domains585_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case585_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family585) : False :=
  FourSquareCase.impossible data585 family585 data585_checked forced585 p hf

#print axioms case585_impossible
end N12Compact.FourSquareCases

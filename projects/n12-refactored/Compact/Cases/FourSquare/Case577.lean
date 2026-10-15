import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 577: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family577 : Finset Nat := {1,2,8,48,192,512,1024,2048,4096,8448,16384,32768}

def domain577_1 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain577_2 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain577_8 : CertifiedDomain family577 :=
  OwnerBudget.product family577 8
    (HalfDomain.ofSpec family577 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family577 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain577_512 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain577_1024 : CertifiedDomain family577 :=
  OwnerBudget.product family577 1024
    (HalfDomain.ofSpec family577 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family577 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain577_2048 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain577_4096 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain577_8448 : CertifiedDomain family577 :=
  OwnerBudget.product family577 8448
    (HalfDomain.ofSpec family577 singleSpec72 0 singleSpec72_checked (by decide +kernel))
    (HalfDomain.ofSpec family577 singleSpec73 1 singleSpec73_checked (by decide +kernel))

def domain577_16384 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain577_32768 : CertifiedDomain family577 :=
  CertifiedDomain.ofCombined family577 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains577 : List (CertifiedDomain family577) :=
  [domain577_1,domain577_2,domain577_8,domain577_4096,domain577_16384,domain577_32768,domain577_512,domain577_1024,domain577_2048,domain577_8448]

theorem domains577_members : ∀ d ∈ domains577, d.mask ∈ family577 := by decide +kernel
theorem domains577_distinct : domains577.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data577 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data577_checked : (data577).Check family577 := by decide +kernel

theorem forced577 (p : NormalizedPacking) (hf : codedMarkerFamily p = family577) :
    ∀ i, natCombinedOwners p (ownerIndex p (data577.masks i)) = data577.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains577 domains577_members domains577_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains577 domains577_members domains577_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains577 domains577_members domains577_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains577 domains577_members domains577_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case577_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family577) : False :=
  FourSquareCase.impossible data577 family577 data577_checked forced577 p hf

#print axioms case577_impossible
end N12Compact.FourSquareCases

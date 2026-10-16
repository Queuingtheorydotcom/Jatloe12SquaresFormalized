import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 565: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family565 : Finset Nat := {1,2,8,48,192,256,1024,2048,4096,8192,16384,32768}

def domain565_1 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain565_2 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain565_8 : CertifiedDomain family565 :=
  OwnerBudget.product family565 8
    (HalfDomain.ofSpec family565 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family565 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain565_256 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain565_1024 : CertifiedDomain family565 :=
  OwnerBudget.product family565 1024
    (HalfDomain.ofSpec family565 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family565 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain565_2048 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain565_4096 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain565_8192 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain565_16384 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain565_32768 : CertifiedDomain family565 :=
  CertifiedDomain.ofCombined family565 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains565 : List (CertifiedDomain family565) :=
  [domain565_1,domain565_2,domain565_8,domain565_4096,domain565_8192,domain565_16384,domain565_32768,domain565_256,domain565_1024,domain565_2048]

theorem domains565_members : ∀ d ∈ domains565, d.mask ∈ family565 := by decide +kernel
theorem domains565_distinct : domains565.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data565 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data565_checked : (data565).Check family565 := by decide +kernel

theorem forced565 (p : NormalizedPacking) (hf : codedMarkerFamily p = family565) :
    ∀ i, natCombinedOwners p (ownerIndex p (data565.masks i)) = data565.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains565 domains565_members domains565_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains565 domains565_members domains565_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains565 domains565_members domains565_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains565 domains565_members domains565_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case565_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family565) : False :=
  FourSquareCase.impossible data565 family565 data565_checked forced565 p hf

#print axioms case565_impossible
end N12Compact.FourSquareCases

import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 575: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family575 : Finset Nat := {1,2,8,48,192,512,1024,2048,4096,8192,16384,32768}

def domain575_1 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain575_2 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain575_8 : CertifiedDomain family575 :=
  OwnerBudget.product family575 8
    (HalfDomain.ofSpec family575 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family575 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain575_512 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain575_1024 : CertifiedDomain family575 :=
  OwnerBudget.product family575 1024
    (HalfDomain.ofSpec family575 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family575 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain575_2048 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain575_4096 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain575_8192 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain575_16384 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain575_32768 : CertifiedDomain family575 :=
  CertifiedDomain.ofCombined family575 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains575 : List (CertifiedDomain family575) :=
  [domain575_1,domain575_2,domain575_8,domain575_4096,domain575_8192,domain575_16384,domain575_32768,domain575_512,domain575_1024,domain575_2048]

theorem domains575_members : ∀ d ∈ domains575, d.mask ∈ family575 := by decide +kernel
theorem domains575_distinct : domains575.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data575 : FourSquareCase.Data :=
  ⟨⟨false,true,false⟩, ![2048,1024,16384,4096],
    ![{5,13},{7,17},{9,19},{1,11}], 8, 2⟩

theorem data575_checked : (data575).Check family575 := by decide +kernel

theorem forced575 (p : NormalizedPacking) (hf : codedMarkerFamily p = family575) :
    ∀ i, natCombinedOwners p (ownerIndex p (data575.masks i)) = data575.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains575 domains575_members domains575_distinct
      2048 {5,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains575 domains575_members domains575_distinct
      1024 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains575 domains575_members domains575_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains575 domains575_members domains575_distinct
      4096 {1,11} (by decide +kernel) p hf

theorem case575_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family575) : False :=
  FourSquareCase.impossible data575 family575 data575_checked forced575 p hf

#print axioms case575_impossible
end N12Compact.FourSquareCases

import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 556: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family556 : Finset Nat := {1,2,8,48,192,256,516,1024,2048,4096,16384,32768}

def domain556_1 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain556_2 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain556_8 : CertifiedDomain family556 :=
  OwnerBudget.product family556 8
    (HalfDomain.ofSpec family556 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family556 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain556_256 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain556_516 : CertifiedDomain family556 :=
  OwnerBudget.product family556 516
    (HalfDomain.ofSpec family556 singleSpec29 0 singleSpec29_checked (by decide +kernel))
    (HalfDomain.ofSpec family556 singleSpec30 1 singleSpec30_checked (by decide +kernel))

def domain556_1024 : CertifiedDomain family556 :=
  OwnerBudget.product family556 1024
    (HalfDomain.ofSpec family556 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family556 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain556_2048 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain556_4096 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain556_16384 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain556_32768 : CertifiedDomain family556 :=
  CertifiedDomain.ofCombined family556 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains556 : List (CertifiedDomain family556) :=
  [domain556_1,domain556_2,domain556_8,domain556_4096,domain556_16384,domain556_32768,domain556_516,domain556_256,domain556_1024,domain556_2048]

theorem domains556_members : ∀ d ∈ domains556, d.mask ∈ family556 := by decide +kernel
theorem domains556_distinct : domains556.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data556 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data556_checked : (data556).Check family556 := by decide +kernel

theorem forced556 (p : NormalizedPacking) (hf : codedMarkerFamily p = family556) :
    ∀ i, natCombinedOwners p (ownerIndex p (data556.masks i)) = data556.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains556 domains556_members domains556_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains556 domains556_members domains556_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains556 domains556_members domains556_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains556 domains556_members domains556_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case556_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family556) : False :=
  FourSquareCase.impossible data556 family556 data556_checked forced556 p hf

#print axioms case556_impossible
end N12Compact.FourSquareCases

import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 454, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family454 : Finset Nat := {1,2,4,48,192,520,1024,2048,4096,8448,16384,32768}

def domain454_1 : CertifiedDomain family454 :=
  CertifiedDomain.ofCombined family454 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain454_2 : CertifiedDomain family454 :=
  CertifiedDomain.ofCombined family454 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain454_4 : CertifiedDomain family454 :=
  OwnerBudget.product family454 4
    (HalfDomain.ofSpec family454 singleSpec8 0 singleSpec8_checked (by decide +kernel))
    (HalfDomain.ofSpec family454 singleSpec10 1 singleSpec10_checked (by decide +kernel))

def domain454_520 : CertifiedDomain family454 :=
  CornerPairDomain.domain520 family454 (by decide +kernel) (by decide +kernel)

def domain454_1024 : CertifiedDomain family454 :=
  OwnerBudget.product family454 1024
    (HalfDomain.ofSpec family454 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family454 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain454_2048 : CertifiedDomain family454 :=
  CertifiedDomain.ofCombined family454 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain454_4096 : CertifiedDomain family454 :=
  CertifiedDomain.ofCombined family454 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain454_8448 : CertifiedDomain family454 :=
  OwnerBudget.product family454 8448
    (HalfDomain.ofSpec family454 singleSpec72 0 singleSpec72_checked (by decide +kernel))
    (HalfDomain.ofSpec family454 singleSpec73 1 singleSpec73_checked (by decide +kernel))

def domain454_16384 : CertifiedDomain family454 :=
  CertifiedDomain.ofCombined family454 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain454_32768 : CertifiedDomain family454 :=
  CertifiedDomain.ofCombined family454 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains454 : List (CertifiedDomain family454) :=
  [domain454_1,domain454_2,domain454_4,domain454_4096,domain454_16384,domain454_32768,domain454_1024,domain454_2048,domain454_8448,domain454_520]

theorem domains454_members : ∀ d ∈ domains454, d.mask ∈ family454 := by decide +kernel
theorem domains454_distinct : domains454.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data454 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,520],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[],[]]⟩

theorem data454_checked : data454.Check family454 := by decide +kernel

theorem forced454 (p : NormalizedPacking) (hf : codedMarkerFamily p = family454) :
    ∀ i, natCombinedOwners p (ownerIndex p (data454.masks i)) = data454.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains454 domains454_members domains454_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains454 domains454_members domains454_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains454 domains454_members domains454_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains454 domains454_members domains454_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains454 domains454_members domains454_distinct
      520 {8,18} (by decide +kernel) p hf

theorem case454_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family454) : False :=
  FourSquareConvexCase.impossible data454 family454 data454_checked forced454 p hf

#print axioms case454_impossible
end
end N12Compact.FourSquareConvexCases

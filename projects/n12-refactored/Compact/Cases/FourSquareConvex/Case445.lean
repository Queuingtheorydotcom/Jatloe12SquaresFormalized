import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 445, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family445 : Finset Nat := {1,2,4,48,192,512,1024,2048,4096,8448,16384,32768}

def domain445_1 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain445_2 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain445_4 : CertifiedDomain family445 :=
  OwnerBudget.product family445 4
    (HalfDomain.ofSpec family445 singleSpec8 0 singleSpec8_checked (by decide +kernel))
    (HalfDomain.ofSpec family445 singleSpec10 1 singleSpec10_checked (by decide +kernel))

def domain445_512 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain445_1024 : CertifiedDomain family445 :=
  OwnerBudget.product family445 1024
    (HalfDomain.ofSpec family445 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family445 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain445_2048 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain445_4096 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain445_8448 : CertifiedDomain family445 :=
  OwnerBudget.product family445 8448
    (HalfDomain.ofSpec family445 singleSpec72 0 singleSpec72_checked (by decide +kernel))
    (HalfDomain.ofSpec family445 singleSpec73 1 singleSpec73_checked (by decide +kernel))

def domain445_16384 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain445_32768 : CertifiedDomain family445 :=
  CertifiedDomain.ofCombined family445 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains445 : List (CertifiedDomain family445) :=
  [domain445_1,domain445_2,domain445_4,domain445_4096,domain445_16384,domain445_32768,domain445_512,domain445_1024,domain445_2048,domain445_8448]

theorem domains445_members : ∀ d ∈ domains445, d.mask ∈ family445 := by decide +kernel
theorem domains445_distinct : domains445.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data445 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[],[]]⟩

theorem data445_checked : data445.Check family445 := by decide +kernel

theorem forced445 (p : NormalizedPacking) (hf : codedMarkerFamily p = family445) :
    ∀ i, natCombinedOwners p (ownerIndex p (data445.masks i)) = data445.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains445 domains445_members domains445_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains445 domains445_members domains445_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains445 domains445_members domains445_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains445 domains445_members domains445_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains445 domains445_members domains445_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case445_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family445) : False :=
  FourSquareConvexCase.impossible data445 family445 data445_checked forced445 p hf

#print axioms case445_impossible
end
end N12Compact.FourSquareConvexCases

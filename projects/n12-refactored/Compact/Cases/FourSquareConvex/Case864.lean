import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 864, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family864 : Finset Nat := {1,2,12,16,192,256,512,2048,4096,8192,16416,33792}

def domain864_1 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain864_2 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain864_16 : CertifiedDomain family864 :=
  OwnerBudget.product family864 16
    (HalfDomain.ofSpec family864 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family864 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain864_256 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain864_512 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain864_2048 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain864_4096 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain864_8192 : CertifiedDomain family864 :=
  CertifiedDomain.ofCombined family864 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain864_16416 : CertifiedDomain family864 :=
  OwnerBudget.product family864 16416
    (HalfDomain.ofSpec family864 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family864 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain864_33792 : CertifiedDomain family864 :=
  UpperMidDomain.domain33792 family864 (by decide +kernel) (by decide +kernel)

def domains864 : List (CertifiedDomain family864) :=
  [domain864_1,domain864_2,domain864_16,domain864_16416,domain864_4096,domain864_8192,domain864_33792,domain864_256,domain864_512,domain864_2048]

theorem domains864_members : ∀ d ∈ domains864, d.mask ∈ family864 := by decide +kernel
theorem domains864_distinct : domains864.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data864 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![33792,2048,4096,16416,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[⟨(3,9/4),(3,11/4),(3,9/4),(3,12/5),3/10,0⟩],[]]⟩

theorem data864_checked : data864.Check family864 := by decide +kernel

theorem forced864 (p : NormalizedPacking) (hf : codedMarkerFamily p = family864) :
    ∀ i, natCombinedOwners p (ownerIndex p (data864.masks i)) = data864.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains864 domains864_members domains864_distinct
      33792 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains864 domains864_members domains864_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains864 domains864_members domains864_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains864 domains864_members domains864_distinct
      16416 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains864 domains864_members domains864_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case864_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family864) : False :=
  FourSquareConvexCase.impossible data864 family864 data864_checked forced864 p hf

#print axioms case864_impossible
end
end N12Compact.FourSquareConvexCases

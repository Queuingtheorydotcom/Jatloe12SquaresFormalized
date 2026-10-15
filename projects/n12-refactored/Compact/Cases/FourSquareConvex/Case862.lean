import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 862, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family862 : Finset Nat := {1,2,12,16,192,256,512,2048,4096,8192,16384,33792}

def domain862_1 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain862_2 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain862_16 : CertifiedDomain family862 :=
  OwnerBudget.product family862 16
    (HalfDomain.ofSpec family862 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family862 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain862_256 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain862_512 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain862_2048 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain862_4096 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain862_8192 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain862_16384 : CertifiedDomain family862 :=
  CertifiedDomain.ofCombined family862 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain862_33792 : CertifiedDomain family862 :=
  UpperMidDomain.domain33792 family862 (by decide +kernel) (by decide +kernel)

def domains862 : List (CertifiedDomain family862) :=
  [domain862_1,domain862_2,domain862_16,domain862_4096,domain862_8192,domain862_16384,domain862_33792,domain862_256,domain862_512,domain862_2048]

theorem domains862_members : ∀ d ∈ domains862, d.mask ∈ family862 := by decide +kernel
theorem domains862_distinct : domains862.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data862 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![33792,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[],[]]⟩

theorem data862_checked : data862.Check family862 := by decide +kernel

theorem forced862 (p : NormalizedPacking) (hf : codedMarkerFamily p = family862) :
    ∀ i, natCombinedOwners p (ownerIndex p (data862.masks i)) = data862.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains862 domains862_members domains862_distinct
      33792 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains862 domains862_members domains862_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains862 domains862_members domains862_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains862 domains862_members domains862_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains862 domains862_members domains862_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case862_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family862) : False :=
  FourSquareConvexCase.impossible data862 family862 data862_checked forced862 p hf

#print axioms case862_impossible
end
end N12Compact.FourSquareConvexCases

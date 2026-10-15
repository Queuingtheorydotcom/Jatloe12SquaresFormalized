import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 998, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family998 : Finset Nat := {1,2,12,192,256,512,1024,2048,4096,8192,16384,32768}

def domain998_1 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain998_2 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain998_256 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain998_512 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain998_1024 : CertifiedDomain family998 :=
  OwnerBudget.product family998 1024
    (HalfDomain.ofSpec family998 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family998 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain998_2048 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain998_4096 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain998_8192 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain998_16384 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain998_32768 : CertifiedDomain family998 :=
  CertifiedDomain.ofCombined family998 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains998 : List (CertifiedDomain family998) :=
  [domain998_1,domain998_2,domain998_4096,domain998_8192,domain998_16384,domain998_32768,domain998_256,domain998_512,domain998_1024,domain998_2048]

theorem domains998_members : ∀ d ∈ domains998, d.mask ∈ family998 := by decide +kernel
theorem domains998_distinct : domains998.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data998 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[],[]]⟩

theorem data998_checked : data998.Check family998 := by decide +kernel

theorem forced998 (p : NormalizedPacking) (hf : codedMarkerFamily p = family998) :
    ∀ i, natCombinedOwners p (ownerIndex p (data998.masks i)) = data998.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains998 domains998_members domains998_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains998 domains998_members domains998_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains998 domains998_members domains998_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains998 domains998_members domains998_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains998 domains998_members domains998_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case998_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family998) : False :=
  FourSquareConvexCase.impossible data998 family998 data998_checked forced998 p hf

#print axioms case998_impossible
end
end N12Compact.FourSquareConvexCases

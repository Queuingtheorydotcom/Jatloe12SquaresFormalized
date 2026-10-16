import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 995, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family995 : Finset Nat := {1,2,12,48,256,512,1024,2176,4096,8192,16384,32768}

def domain995_1 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain995_2 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain995_256 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain995_512 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain995_1024 : CertifiedDomain family995 :=
  OwnerBudget.product family995 1024
    (HalfDomain.ofSpec family995 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family995 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain995_2176 : CertifiedDomain family995 :=
  OwnerBudget.product family995 2176
    (HalfDomain.ofSpec family995 singleSpec46 0 singleSpec46_checked (by decide +kernel))
    (HalfDomain.singleton family995 2176 1 (by decide +kernel) (by decide +kernel))

def domain995_4096 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain995_8192 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain995_16384 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain995_32768 : CertifiedDomain family995 :=
  CertifiedDomain.ofCombined family995 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains995 : List (CertifiedDomain family995) :=
  [domain995_1,domain995_2,domain995_4096,domain995_8192,domain995_16384,domain995_32768,domain995_256,domain995_512,domain995_1024,domain995_2176]

theorem domains995_members : ∀ d ∈ domains995, d.mask ∈ family995 := by decide +kernel
theorem domains995_distinct : domains995.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data995 : FourSquareConvexCase.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768,2176],
    ![{5,16},{8,18},{6,15},{7,17},{3,14}], 1,
    ![[],[],[],[],[]]⟩

theorem data995_checked : data995.Check family995 := by decide +kernel

theorem forced995 (p : NormalizedPacking) (hf : codedMarkerFamily p = family995) :
    ∀ i, natCombinedOwners p (ownerIndex p (data995.masks i)) = data995.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains995 domains995_members domains995_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains995 domains995_members domains995_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains995 domains995_members domains995_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains995 domains995_members domains995_distinct
      32768 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains995 domains995_members domains995_distinct
      2176 {3,14} (by decide +kernel) p hf

theorem case995_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family995) : False :=
  FourSquareConvexCase.impossible data995 family995 data995_checked forced995 p hf

#print axioms case995_impossible
end
end N12Compact.FourSquareConvexCases

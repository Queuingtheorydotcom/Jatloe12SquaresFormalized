import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1070: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1070 : Finset Nat := {1,8,48,192,258,512,1024,2048,4096,8196,16384,32768}

def domain1070_1 : CertifiedDomain family1070 :=
  CertifiedDomain.ofCombined family1070 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1070_8 : CertifiedDomain family1070 :=
  OwnerBudget.product family1070 8
    (HalfDomain.ofSpec family1070 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family1070 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain1070_258 : CertifiedDomain family1070 :=
  OwnerBudget.product family1070 258
    (HalfDomain.ofSpec family1070 singleSpec24 0 singleSpec24_checked (by decide +kernel))
    (HalfDomain.singleton family1070 258 1 (by decide +kernel) (by decide +kernel))

def domain1070_512 : CertifiedDomain family1070 :=
  CertifiedDomain.ofCombined family1070 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1070_1024 : CertifiedDomain family1070 :=
  OwnerBudget.product family1070 1024
    (HalfDomain.ofSpec family1070 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1070 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1070_2048 : CertifiedDomain family1070 :=
  CertifiedDomain.ofCombined family1070 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1070_4096 : CertifiedDomain family1070 :=
  CertifiedDomain.ofCombined family1070 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain1070_8196 : CertifiedDomain family1070 :=
  OwnerBudget.product family1070 8196
    (HalfDomain.ofSpec family1070 singleSpec70 0 singleSpec70_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family1070 8196 1 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain1070_16384 : CertifiedDomain family1070 :=
  CertifiedDomain.ofCombined family1070 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain1070_32768 : CertifiedDomain family1070 :=
  CertifiedDomain.ofCombined family1070 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1070 : List (CertifiedDomain family1070) :=
  [domain1070_1,domain1070_8,domain1070_8196,domain1070_4096,domain1070_16384,domain1070_32768,domain1070_512,domain1070_1024,domain1070_2048,domain1070_258]

theorem domains1070_members : ∀ d ∈ domains1070, d.mask ∈ family1070 := by decide +kernel
theorem domains1070_distinct : domains1070.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1070 : FourSquareCaseVariant.Data :=
  ⟨⟨false,true,false⟩, ![2048,1024,16384,4096,258],
    ![{5,13},{7,17},{9,19},{1,11},{0,10}], 8⟩

theorem data1070_checked : (data1070).Check family1070 := by decide +kernel

theorem forced1070 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1070) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1070.masks i)) = data1070.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1070 domains1070_members domains1070_distinct
      2048 {5,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains1070 domains1070_members domains1070_distinct
      1024 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains1070 domains1070_members domains1070_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains1070 domains1070_members domains1070_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains1070 domains1070_members domains1070_distinct
      258 {0,10} (by decide +kernel) p hf

theorem case1070_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1070) : False :=
  FourSquareCaseVariant.impossible data1070 family1070 data1070_checked forced1070 p hf

#print axioms case1070_impossible
end N12Compact.FourSquareVariantCases

import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1069: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1069 : Finset Nat := {1,8,48,192,258,512,1024,2048,4096,8192,16384,32768}

def domain1069_1 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1069_8 : CertifiedDomain family1069 :=
  OwnerBudget.product family1069 8
    (HalfDomain.ofSpec family1069 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family1069 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain1069_258 : CertifiedDomain family1069 :=
  OwnerBudget.product family1069 258
    (HalfDomain.ofSpec family1069 singleSpec24 0 singleSpec24_checked (by decide +kernel))
    (HalfDomain.singleton family1069 258 1 (by decide +kernel) (by decide +kernel))

def domain1069_512 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1069_1024 : CertifiedDomain family1069 :=
  OwnerBudget.product family1069 1024
    (HalfDomain.ofSpec family1069 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1069 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1069_2048 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1069_4096 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain1069_8192 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1069_16384 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain1069_32768 : CertifiedDomain family1069 :=
  CertifiedDomain.ofCombined family1069 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1069 : List (CertifiedDomain family1069) :=
  [domain1069_1,domain1069_8,domain1069_4096,domain1069_8192,domain1069_16384,domain1069_32768,domain1069_512,domain1069_1024,domain1069_2048,domain1069_258]

theorem domains1069_members : ∀ d ∈ domains1069, d.mask ∈ family1069 := by decide +kernel
theorem domains1069_distinct : domains1069.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1069 : FourSquareCaseVariant.Data :=
  ⟨⟨false,true,false⟩, ![2048,1024,16384,4096,258],
    ![{5,13},{7,17},{9,19},{1,11},{0,10}], 8⟩

theorem data1069_checked : (data1069).Check family1069 := by decide +kernel

theorem forced1069 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1069) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1069.masks i)) = data1069.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1069 domains1069_members domains1069_distinct
      2048 {5,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains1069 domains1069_members domains1069_distinct
      1024 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains1069 domains1069_members domains1069_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains1069 domains1069_members domains1069_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains1069 domains1069_members domains1069_distinct
      258 {0,10} (by decide +kernel) p hf

theorem case1069_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1069) : False :=
  FourSquareCaseVariant.impossible data1069 family1069 data1069_checked forced1069 p hf

#print axioms case1069_impossible
end N12Compact.FourSquareVariantCases

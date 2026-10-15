import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1063: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1063 : Finset Nat := {1,8,48,192,256,512,1024,2048,4096,8192,16384,32768}

def domain1063_1 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1063_8 : CertifiedDomain family1063 :=
  OwnerBudget.product family1063 8
    (HalfDomain.ofSpec family1063 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family1063 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain1063_256 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1063_512 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1063_1024 : CertifiedDomain family1063 :=
  OwnerBudget.product family1063 1024
    (HalfDomain.ofSpec family1063 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1063 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1063_2048 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1063_4096 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain1063_8192 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1063_16384 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain1063_32768 : CertifiedDomain family1063 :=
  CertifiedDomain.ofCombined family1063 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1063 : List (CertifiedDomain family1063) :=
  [domain1063_1,domain1063_8,domain1063_4096,domain1063_8192,domain1063_16384,domain1063_32768,domain1063_256,domain1063_512,domain1063_1024,domain1063_2048]

theorem domains1063_members : ∀ d ∈ domains1063, d.mask ∈ family1063 := by decide +kernel
theorem domains1063_distinct : domains1063.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1063 : FourSquareCaseVariant.Data :=
  ⟨⟨false,true,false⟩, ![2048,1024,16384,4096,256],
    ![{5,13},{7,17},{9,19},{1,11},{0,10}], 8⟩

theorem data1063_checked : (data1063).Check family1063 := by decide +kernel

theorem forced1063 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1063) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1063.masks i)) = data1063.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1063 domains1063_members domains1063_distinct
      2048 {5,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains1063 domains1063_members domains1063_distinct
      1024 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains1063 domains1063_members domains1063_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains1063 domains1063_members domains1063_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains1063 domains1063_members domains1063_distinct
      256 {0,10} (by decide +kernel) p hf

theorem case1063_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1063) : False :=
  FourSquareCaseVariant.impossible data1063 family1063 data1063_checked forced1063 p hf

#print axioms case1063_impossible
end N12Compact.FourSquareVariantCases

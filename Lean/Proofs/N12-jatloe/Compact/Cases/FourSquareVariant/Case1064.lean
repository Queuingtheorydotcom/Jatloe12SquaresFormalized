import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1064: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1064 : Finset Nat := {1,8,48,192,256,512,1024,2048,4096,8196,16384,32768}

def domain1064_1 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1064_8 : CertifiedDomain family1064 :=
  OwnerBudget.product family1064 8
    (HalfDomain.ofSpec family1064 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family1064 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain1064_256 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1064_512 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1064_1024 : CertifiedDomain family1064 :=
  OwnerBudget.product family1064 1024
    (HalfDomain.ofSpec family1064 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1064 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1064_2048 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1064_4096 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain1064_8196 : CertifiedDomain family1064 :=
  OwnerBudget.product family1064 8196
    (HalfDomain.ofSpec family1064 singleSpec70 0 singleSpec70_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family1064 8196 1 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain1064_16384 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain1064_32768 : CertifiedDomain family1064 :=
  CertifiedDomain.ofCombined family1064 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1064 : List (CertifiedDomain family1064) :=
  [domain1064_1,domain1064_8,domain1064_8196,domain1064_4096,domain1064_16384,domain1064_32768,domain1064_256,domain1064_512,domain1064_1024,domain1064_2048]

theorem domains1064_members : ∀ d ∈ domains1064, d.mask ∈ family1064 := by decide +kernel
theorem domains1064_distinct : domains1064.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1064 : FourSquareCaseVariant.Data :=
  ⟨⟨false,true,false⟩, ![2048,1024,16384,4096,256],
    ![{5,13},{7,17},{9,19},{1,11},{0,10}], 8⟩

theorem data1064_checked : (data1064).Check family1064 := by decide +kernel

theorem forced1064 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1064) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1064.masks i)) = data1064.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1064 domains1064_members domains1064_distinct
      2048 {5,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains1064 domains1064_members domains1064_distinct
      1024 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains1064 domains1064_members domains1064_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains1064 domains1064_members domains1064_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains1064 domains1064_members domains1064_distinct
      256 {0,10} (by decide +kernel) p hf

theorem case1064_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1064) : False :=
  FourSquareCaseVariant.impossible data1064 family1064 data1064_checked forced1064 p hf

#print axioms case1064_impossible
end N12Compact.FourSquareVariantCases

import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 999: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family999 : Finset Nat := {1,2,12,192,256,512,1024,2048,4096,8192,16384,32784}

def domain999_1 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain999_2 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain999_256 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain999_512 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain999_1024 : CertifiedDomain family999 :=
  OwnerBudget.product family999 1024
    (HalfDomain.ofSpec family999 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family999 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain999_2048 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain999_4096 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain999_8192 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain999_16384 : CertifiedDomain family999 :=
  CertifiedDomain.ofCombined family999 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain999_32784 : CertifiedDomain family999 :=
  OwnerBudget.product family999 32784
    (HalfDomain.ofSeedHull family999 32784 0 7 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,3),(11/4,3),(9/4,3),(12/5,3),3/10,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSpec family999 singleSpec92 1 singleSpec92_checked (by decide +kernel))

def domains999 : List (CertifiedDomain family999) :=
  [domain999_1,domain999_2,domain999_32784,domain999_4096,domain999_8192,domain999_16384,domain999_256,domain999_512,domain999_1024,domain999_2048]

theorem domains999_members : ∀ d ∈ domains999, d.mask ∈ family999 := by decide +kernel
theorem domains999_distinct : domains999.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data999 : FourSquareCaseVariant.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2⟩

theorem data999_checked : (data999).Check family999 := by decide +kernel

theorem forced999 (p : NormalizedPacking) (hf : codedMarkerFamily p = family999) :
    ∀ i, natCombinedOwners p (ownerIndex p (data999.masks i)) = data999.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains999 domains999_members domains999_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains999 domains999_members domains999_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains999 domains999_members domains999_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains999 domains999_members domains999_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains999 domains999_members domains999_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case999_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family999) : False :=
  FourSquareCaseVariant.impossible data999 family999 data999_checked forced999 p hf

#print axioms case999_impossible
end N12Compact.FourSquareVariantCases

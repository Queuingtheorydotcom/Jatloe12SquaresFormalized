import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 990: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family990 : Finset Nat := {1,2,12,48,256,512,1024,2048,4224,8192,16384,32768}

def domain990_1 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain990_2 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain990_256 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain990_512 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain990_1024 : CertifiedDomain family990 :=
  OwnerBudget.product family990 1024
    (HalfDomain.ofSpec family990 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family990 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain990_2048 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain990_4224 : CertifiedDomain family990 :=
  OwnerBudget.product family990 4224
    (HalfDomain.ofSeedHull family990 4224 0 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(1,9/4),(1,11/4),(1,9/4),(1,113/50),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSpec family990 singleSpec61 1 singleSpec61_checked (by decide +kernel))

def domain990_8192 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain990_16384 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain990_32768 : CertifiedDomain family990 :=
  CertifiedDomain.ofCombined family990 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains990 : List (CertifiedDomain family990) :=
  [domain990_1,domain990_2,domain990_4224,domain990_8192,domain990_16384,domain990_32768,domain990_256,domain990_512,domain990_1024,domain990_2048]

theorem domains990_members : ∀ d ∈ domains990, d.mask ∈ family990 := by decide +kernel
theorem domains990_distinct : domains990.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data990 : FourSquareCaseVariant.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768,2048],
    ![{5,16},{8,18},{6,15},{7,17},{3,14}], 1⟩

theorem data990_checked : (data990).Check family990 := by decide +kernel

theorem forced990 (p : NormalizedPacking) (hf : codedMarkerFamily p = family990) :
    ∀ i, natCombinedOwners p (ownerIndex p (data990.masks i)) = data990.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains990 domains990_members domains990_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains990 domains990_members domains990_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains990 domains990_members domains990_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains990 domains990_members domains990_distinct
      32768 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains990 domains990_members domains990_distinct
      2048 {3,14} (by decide +kernel) p hf

theorem case990_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family990) : False :=
  FourSquareCaseVariant.impossible data990 family990 data990_checked forced990 p hf

#print axioms case990_impossible
end N12Compact.FourSquareVariantCases

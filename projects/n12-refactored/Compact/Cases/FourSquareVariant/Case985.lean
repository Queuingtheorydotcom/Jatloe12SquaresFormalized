import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 985: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family985 : Finset Nat := {1,2,12,48,256,512,1024,2048,4096,8192,16384,32768}

def domain985_1 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain985_2 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain985_256 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain985_512 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain985_1024 : CertifiedDomain family985 :=
  OwnerBudget.product family985 1024
    (HalfDomain.ofSpec family985 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family985 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain985_2048 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain985_4096 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain985_8192 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain985_16384 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain985_32768 : CertifiedDomain family985 :=
  CertifiedDomain.ofCombined family985 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains985 : List (CertifiedDomain family985) :=
  [domain985_1,domain985_2,domain985_4096,domain985_8192,domain985_16384,domain985_32768,domain985_256,domain985_512,domain985_1024,domain985_2048]

theorem domains985_members : ∀ d ∈ domains985, d.mask ∈ family985 := by decide +kernel
theorem domains985_distinct : domains985.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data985 : FourSquareCaseVariant.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768,2048],
    ![{5,16},{8,18},{6,15},{7,17},{3,14}], 1⟩

theorem data985_checked : (data985).Check family985 := by decide +kernel

theorem forced985 (p : NormalizedPacking) (hf : codedMarkerFamily p = family985) :
    ∀ i, natCombinedOwners p (ownerIndex p (data985.masks i)) = data985.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains985 domains985_members domains985_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains985 domains985_members domains985_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains985 domains985_members domains985_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains985 domains985_members domains985_distinct
      32768 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains985 domains985_members domains985_distinct
      2048 {3,14} (by decide +kernel) p hf

theorem case985_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family985) : False :=
  FourSquareCaseVariant.impossible data985 family985 data985_checked forced985 p hf

#print axioms case985_impossible
end N12Compact.FourSquareVariantCases

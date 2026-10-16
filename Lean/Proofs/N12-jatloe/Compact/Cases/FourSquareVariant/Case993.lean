import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.CornerPairDomain
import S12.DomainSpecData

/-! Original marker case 993: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family993 : Finset Nat := {1,2,12,48,256,512,1024,2112,4096,8192,16384,32768}

def domain993_1 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain993_2 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain993_256 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain993_512 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain993_1024 : CertifiedDomain family993 :=
  OwnerBudget.product family993 1024
    (HalfDomain.ofSpec family993 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family993 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain993_2112 : CertifiedDomain family993 :=
  CornerPairDomain.domain2112 family993 (by decide +kernel) (by decide +kernel)

def domain993_4096 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain993_8192 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain993_16384 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain993_32768 : CertifiedDomain family993 :=
  CertifiedDomain.ofCombined family993 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains993 : List (CertifiedDomain family993) :=
  [domain993_1,domain993_2,domain993_4096,domain993_8192,domain993_16384,domain993_32768,domain993_256,domain993_512,domain993_1024,domain993_2112]

theorem domains993_members : ∀ d ∈ domains993, d.mask ∈ family993 := by decide +kernel
theorem domains993_distinct : domains993.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data993 : FourSquareCaseVariant.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768,2112],
    ![{5,16},{8,18},{6,15},{7,17},{3,14}], 1⟩

theorem data993_checked : (data993).Check family993 := by decide +kernel

theorem forced993 (p : NormalizedPacking) (hf : codedMarkerFamily p = family993) :
    ∀ i, natCombinedOwners p (ownerIndex p (data993.masks i)) = data993.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains993 domains993_members domains993_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains993 domains993_members domains993_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains993 domains993_members domains993_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains993 domains993_members domains993_distinct
      32768 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains993 domains993_members domains993_distinct
      2112 {3,14} (by decide +kernel) p hf

theorem case993_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family993) : False :=
  FourSquareCaseVariant.impossible data993 family993 data993_checked forced993 p hf

#print axioms case993_impossible
end
end N12Compact.FourSquareVariantCases

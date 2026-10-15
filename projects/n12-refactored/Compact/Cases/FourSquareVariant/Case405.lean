import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 405: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family405 : Finset Nat := {1,2,4,48,192,256,512,1024,2048,4096,16384,32768}

def domain405_1 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain405_2 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain405_4 : CertifiedDomain family405 :=
  OwnerBudget.product family405 4
    (HalfDomain.ofSpec family405 singleSpec8 0 singleSpec8_checked (by decide +kernel))
    (HalfDomain.ofSpec family405 singleSpec10 1 singleSpec10_checked (by decide +kernel))

def domain405_256 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain405_512 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain405_1024 : CertifiedDomain family405 :=
  OwnerBudget.product family405 1024
    (HalfDomain.ofSpec family405 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family405 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain405_2048 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain405_4096 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain405_16384 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain405_32768 : CertifiedDomain family405 :=
  CertifiedDomain.ofCombined family405 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains405 : List (CertifiedDomain family405) :=
  [domain405_1,domain405_2,domain405_4,domain405_4096,domain405_16384,domain405_32768,domain405_256,domain405_512,domain405_1024,domain405_2048]

theorem domains405_members : ∀ d ∈ domains405, d.mask ∈ family405 := by decide +kernel
theorem domains405_distinct : domains405.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data405 : FourSquareCaseVariant.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2⟩

theorem data405_checked : (data405).Check family405 := by decide +kernel

theorem forced405 (p : NormalizedPacking) (hf : codedMarkerFamily p = family405) :
    ∀ i, natCombinedOwners p (ownerIndex p (data405.masks i)) = data405.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains405 domains405_members domains405_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains405 domains405_members domains405_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains405 domains405_members domains405_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains405 domains405_members domains405_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains405 domains405_members domains405_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case405_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family405) : False :=
  FourSquareCaseVariant.impossible data405 family405 data405_checked forced405 p hf

#print axioms case405_impossible
end N12Compact.FourSquareVariantCases

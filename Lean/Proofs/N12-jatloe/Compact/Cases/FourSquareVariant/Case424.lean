import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.CornerPairDomain
import S12.DomainSpecData

/-! Original marker case 424: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family424 : Finset Nat := {1,2,4,48,192,256,520,1024,2048,4096,16384,32768}

def domain424_1 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain424_2 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain424_4 : CertifiedDomain family424 :=
  OwnerBudget.product family424 4
    (HalfDomain.ofSpec family424 singleSpec8 0 singleSpec8_checked (by decide +kernel))
    (HalfDomain.ofSpec family424 singleSpec10 1 singleSpec10_checked (by decide +kernel))

def domain424_256 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain424_520 : CertifiedDomain family424 :=
  CornerPairDomain.domain520 family424 (by decide +kernel) (by decide +kernel)

def domain424_1024 : CertifiedDomain family424 :=
  OwnerBudget.product family424 1024
    (HalfDomain.ofSpec family424 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family424 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain424_2048 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain424_4096 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain424_16384 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain424_32768 : CertifiedDomain family424 :=
  CertifiedDomain.ofCombined family424 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains424 : List (CertifiedDomain family424) :=
  [domain424_1,domain424_2,domain424_4,domain424_4096,domain424_16384,domain424_32768,domain424_256,domain424_1024,domain424_2048,domain424_520]

theorem domains424_members : ∀ d ∈ domains424, d.mask ∈ family424 := by decide +kernel
theorem domains424_distinct : domains424.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data424 : FourSquareCaseVariant.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,520],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2⟩

theorem data424_checked : (data424).Check family424 := by decide +kernel

theorem forced424 (p : NormalizedPacking) (hf : codedMarkerFamily p = family424) :
    ∀ i, natCombinedOwners p (ownerIndex p (data424.masks i)) = data424.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains424 domains424_members domains424_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains424 domains424_members domains424_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains424 domains424_members domains424_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains424 domains424_members domains424_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains424 domains424_members domains424_distinct
      520 {8,18} (by decide +kernel) p hf

theorem case424_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family424) : False :=
  FourSquareCaseVariant.impossible data424 family424 data424_checked forced424 p hf

#print axioms case424_impossible
end
end N12Compact.FourSquareVariantCases

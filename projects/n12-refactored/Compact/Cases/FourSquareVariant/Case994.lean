import Compact.Bridge.FourSquareCaseVariant
import Compact.Bridge.CornerPairDomain
import S12.DomainSpecData

/-! Original marker case 994: the right row barrier comes from the fifth
actual owner. All auxiliary ownership and point memberships are checked. -/
namespace N12Compact.FourSquareVariantCases
open S12 OwnerBudget FourSquareCaseVariant
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family994 : Finset Nat := {1,2,12,48,256,512,1024,2112,4224,8192,16384,32768}

def domain994_1 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain994_2 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain994_256 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain994_512 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain994_1024 : CertifiedDomain family994 :=
  OwnerBudget.product family994 1024
    (HalfDomain.ofSpec family994 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family994 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain994_2112 : CertifiedDomain family994 :=
  CornerPairDomain.domain2112 family994 (by decide +kernel) (by decide +kernel)

def domain994_4224 : CertifiedDomain family994 :=
  OwnerBudget.product family994 4224
    (HalfDomain.ofSeedHull family994 4224 0 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(1,9/4),(1,11/4),(1,9/4),(1,113/50),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSpec family994 singleSpec61 1 singleSpec61_checked (by decide +kernel))

def domain994_8192 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain994_16384 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain994_32768 : CertifiedDomain family994 :=
  CertifiedDomain.ofCombined family994 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains994 : List (CertifiedDomain family994) :=
  [domain994_1,domain994_2,domain994_4224,domain994_8192,domain994_16384,domain994_32768,domain994_256,domain994_512,domain994_1024,domain994_2112]

theorem domains994_members : ∀ d ∈ domains994, d.mask ∈ family994 := by decide +kernel
theorem domains994_distinct : domains994.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data994 : FourSquareCaseVariant.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768,2112],
    ![{5,16},{8,18},{6,15},{7,17},{3,14}], 1⟩

theorem data994_checked : (data994).Check family994 := by decide +kernel

theorem forced994 (p : NormalizedPacking) (hf : codedMarkerFamily p = family994) :
    ∀ i, natCombinedOwners p (ownerIndex p (data994.masks i)) = data994.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains994 domains994_members domains994_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains994 domains994_members domains994_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains994 domains994_members domains994_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains994 domains994_members domains994_distinct
      32768 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains994 domains994_members domains994_distinct
      2112 {3,14} (by decide +kernel) p hf

theorem case994_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family994) : False :=
  FourSquareCaseVariant.impossible data994 family994 data994_checked forced994 p hf

#print axioms case994_impossible
end
end N12Compact.FourSquareVariantCases

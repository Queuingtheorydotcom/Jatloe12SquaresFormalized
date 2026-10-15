import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 853. Every domain and query-point premise
is derived from the original packing; archived hulls are not assumptions. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family853 : Finset Nat := {1,2,12,16,192,256,512,1024,6144,8192,16416,32768}

def domain853_1 : CertifiedDomain family853 :=
  CertifiedDomain.ofCombined family853 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain853_2 : CertifiedDomain family853 :=
  CertifiedDomain.ofCombined family853 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain853_16 : CertifiedDomain family853 :=
  OwnerBudget.product family853 16
    (HalfDomain.ofSpec family853 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family853 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain853_256 : CertifiedDomain family853 :=
  CertifiedDomain.ofCombined family853 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain853_512 : CertifiedDomain family853 :=
  CertifiedDomain.ofCombined family853 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain853_1024 : CertifiedDomain family853 :=
  OwnerBudget.product family853 1024
    (HalfDomain.ofSpec family853 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family853 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain853_6144 : CertifiedDomain family853 :=
  OwnerBudget.product family853 6144
    (HalfDomain.singleton family853 6144 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.singleton family853 6144 1 (by decide +kernel) (by decide +kernel))

def domain853_8192 : CertifiedDomain family853 :=
  CertifiedDomain.ofCombined family853 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain853_16416 : CertifiedDomain family853 :=
  OwnerBudget.product family853 16416
    (HalfDomain.ofSpec family853 singleSpec82 0 singleSpec82_checked (by decide +kernel))
    (HalfDomain.ofSpec family853 singleSpec83 1 singleSpec83_checked (by decide +kernel))

def domain853_32768 : CertifiedDomain family853 :=
  CertifiedDomain.ofCombined family853 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains853 : List (CertifiedDomain family853) :=
  [domain853_1,domain853_2,domain853_16,domain853_16416,domain853_8192,domain853_32768,domain853_256,domain853_512,domain853_1024,domain853_6144]

theorem domains853_members : ∀ d ∈ domains853, d.mask ∈ family853 := by decide +kernel
theorem domains853_distinct : domains853.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data853 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data853_checked : data853.Check family853 := by decide +kernel

theorem forced853 (p : NormalizedPacking) (hf : codedMarkerFamily p = family853) :
    ∀ i, natCombinedOwners p (ownerIndex p (data853.masks i)) = data853.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains853 domains853_members domains853_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains853 domains853_members domains853_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains853 domains853_members domains853_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains853 domains853_members domains853_distinct
      16 {7,17} (by decide +kernel) p hf

theorem case853_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family853) : False :=
  FourSquareCaseHighRight.impossible data853 family853 data853_checked forced853 p hf

#print axioms case853_impossible
end N12Compact.FourSquareHighRightCases

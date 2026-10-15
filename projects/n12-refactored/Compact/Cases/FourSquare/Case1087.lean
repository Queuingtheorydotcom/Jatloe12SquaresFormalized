import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1087: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1087 : Finset Nat := {1,12,48,64,256,512,1024,2176,4098,8192,16384,32768}

def domain1087_1 : CertifiedDomain family1087 :=
  CertifiedDomain.ofCombined family1087 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1087_64 : CertifiedDomain family1087 :=
  OwnerBudget.product family1087 64
    (HalfDomain.ofSpec family1087 singleSpec19 0 singleSpec19_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family1087 64 1 4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(87/50,3),(87/50,3),(87/50,3),(87/50,3),0,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain1087_256 : CertifiedDomain family1087 :=
  CertifiedDomain.ofCombined family1087 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1087_512 : CertifiedDomain family1087 :=
  CertifiedDomain.ofCombined family1087 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1087_1024 : CertifiedDomain family1087 :=
  OwnerBudget.product family1087 1024
    (HalfDomain.ofSpec family1087 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1087 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1087_2176 : CertifiedDomain family1087 :=
  OwnerBudget.product family1087 2176
    (HalfDomain.ofSpec family1087 singleSpec46 0 singleSpec46_checked (by decide +kernel))
    (HalfDomain.singleton family1087 2176 1 (by decide +kernel) (by decide +kernel))

def domain1087_4098 : CertifiedDomain family1087 :=
  OwnerBudget.product family1087 4098
    (HalfDomain.ofSpec family1087 singleSpec59 0 singleSpec59_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family1087 4098 1 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(1,5/4),(1,7/4),(1,5/4),(1,8/5),7/10,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain1087_8192 : CertifiedDomain family1087 :=
  CertifiedDomain.ofCombined family1087 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1087_16384 : CertifiedDomain family1087 :=
  CertifiedDomain.ofCombined family1087 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain1087_32768 : CertifiedDomain family1087 :=
  CertifiedDomain.ofCombined family1087 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1087 : List (CertifiedDomain family1087) :=
  [domain1087_1,domain1087_64,domain1087_4098,domain1087_8192,domain1087_16384,domain1087_32768,domain1087_256,domain1087_512,domain1087_1024,domain1087_2176]

theorem domains1087_members : ∀ d ∈ domains1087, d.mask ∈ family1087 := by decide +kernel
theorem domains1087_distinct : domains1087.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1087 : FourSquareCase.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768],
    ![{5,16},{8,18},{6,15},{7,17}], 1, 64⟩

theorem data1087_checked : (data1087).Check family1087 := by decide +kernel

theorem forced1087 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1087) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1087.masks i)) = data1087.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1087 domains1087_members domains1087_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains1087 domains1087_members domains1087_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains1087 domains1087_members domains1087_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains1087 domains1087_members domains1087_distinct
      32768 {7,17} (by decide +kernel) p hf

theorem case1087_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1087) : False :=
  FourSquareCase.impossible data1087 family1087 data1087_checked forced1087 p hf

#print axioms case1087_impossible
end N12Compact.FourSquareCases

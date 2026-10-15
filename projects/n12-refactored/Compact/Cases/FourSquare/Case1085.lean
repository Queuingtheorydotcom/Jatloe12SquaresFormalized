import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 1085: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1085 : Finset Nat := {1,12,48,64,256,512,1024,2048,4098,8192,16384,32768}

def domain1085_1 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain1085_64 : CertifiedDomain family1085 :=
  OwnerBudget.product family1085 64
    (HalfDomain.ofSpec family1085 singleSpec19 0 singleSpec19_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family1085 64 1 4 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(87/50,3),(87/50,3),(87/50,3),(87/50,3),0,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain1085_256 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain1085_512 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain1085_1024 : CertifiedDomain family1085 :=
  OwnerBudget.product family1085 1024
    (HalfDomain.ofSpec family1085 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family1085 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain1085_2048 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain1085_4098 : CertifiedDomain family1085 :=
  OwnerBudget.product family1085 4098
    (HalfDomain.ofSpec family1085 singleSpec59 0 singleSpec59_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family1085 4098 1 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(1,5/4),(1,7/4),(1,5/4),(1,8/5),7/10,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain1085_8192 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain1085_16384 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain1085_32768 : CertifiedDomain family1085 :=
  CertifiedDomain.ofCombined family1085 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains1085 : List (CertifiedDomain family1085) :=
  [domain1085_1,domain1085_64,domain1085_4098,domain1085_8192,domain1085_16384,domain1085_32768,domain1085_256,domain1085_512,domain1085_1024,domain1085_2048]

theorem domains1085_members : ∀ d ∈ domains1085, d.mask ∈ family1085 := by decide +kernel
theorem domains1085_distinct : domains1085.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1085 : FourSquareCase.Data :=
  ⟨⟨true,false,false⟩, ![1024,512,8192,32768],
    ![{5,16},{8,18},{6,15},{7,17}], 1, 64⟩

theorem data1085_checked : (data1085).Check family1085 := by decide +kernel

theorem forced1085 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1085) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1085.masks i)) = data1085.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1085 domains1085_members domains1085_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains1085 domains1085_members domains1085_distinct
      512 {8,18} (by decide +kernel) p hf
  · exact certified_domain_forced domains1085 domains1085_members domains1085_distinct
      8192 {6,15} (by decide +kernel) p hf
  · exact certified_domain_forced domains1085 domains1085_members domains1085_distinct
      32768 {7,17} (by decide +kernel) p hf

theorem case1085_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1085) : False :=
  FourSquareCase.impossible data1085 family1085 data1085_checked forced1085 p hf

#print axioms case1085_impossible
end N12Compact.FourSquareCases

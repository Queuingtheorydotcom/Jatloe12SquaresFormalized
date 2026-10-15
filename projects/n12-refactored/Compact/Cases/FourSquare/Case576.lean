import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 576: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family576 : Finset Nat := {1,2,8,48,192,512,1024,2048,4096,8196,16384,32768}

def domain576_1 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain576_2 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain576_8 : CertifiedDomain family576 :=
  OwnerBudget.product family576 8
    (HalfDomain.ofSpec family576 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family576 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain576_512 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain576_1024 : CertifiedDomain family576 :=
  OwnerBudget.product family576 1024
    (HalfDomain.ofSpec family576 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family576 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain576_2048 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain576_4096 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain576_8196 : CertifiedDomain family576 :=
  OwnerBudget.product family576 8196
    (HalfDomain.ofSpec family576 singleSpec70 0 singleSpec70_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family576 8196 1 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain576_16384 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain576_32768 : CertifiedDomain family576 :=
  CertifiedDomain.ofCombined family576 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains576 : List (CertifiedDomain family576) :=
  [domain576_1,domain576_2,domain576_8,domain576_8196,domain576_4096,domain576_16384,domain576_32768,domain576_512,domain576_1024,domain576_2048]

theorem domains576_members : ∀ d ∈ domains576, d.mask ∈ family576 := by decide +kernel
theorem domains576_distinct : domains576.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data576 : FourSquareCase.Data :=
  ⟨⟨false,true,false⟩, ![2048,1024,16384,4096],
    ![{5,13},{7,17},{9,19},{1,11}], 8, 2⟩

theorem data576_checked : (data576).Check family576 := by decide +kernel

theorem forced576 (p : NormalizedPacking) (hf : codedMarkerFamily p = family576) :
    ∀ i, natCombinedOwners p (ownerIndex p (data576.masks i)) = data576.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains576 domains576_members domains576_distinct
      2048 {5,13} (by decide +kernel) p hf
  · exact certified_domain_forced domains576 domains576_members domains576_distinct
      1024 {7,17} (by decide +kernel) p hf
  · exact certified_domain_forced domains576 domains576_members domains576_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains576 domains576_members domains576_distinct
      4096 {1,11} (by decide +kernel) p hf

theorem case576_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family576) : False :=
  FourSquareCase.impossible data576 family576 data576_checked forced576 p hf

#print axioms case576_impossible
end N12Compact.FourSquareCases

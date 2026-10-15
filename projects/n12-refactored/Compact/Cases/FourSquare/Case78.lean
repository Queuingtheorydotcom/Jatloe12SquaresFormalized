import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 78: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family78 : Finset Nat := {1,2,4,8,48,192,1024,2048,4096,8448,16384,32768}

def domain78_1 : CertifiedDomain family78 :=
  CertifiedDomain.ofCombined family78 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain78_2 : CertifiedDomain family78 :=
  CertifiedDomain.ofCombined family78 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain78_4 : CertifiedDomain family78 :=
  OwnerBudget.product family78 4
    (HalfDomain.ofSpec family78 singleSpec8 0 singleSpec8_checked (by decide +kernel))
    (HalfDomain.ofSpec family78 singleSpec10 1 singleSpec10_checked (by decide +kernel))

def domain78_8 : CertifiedDomain family78 :=
  OwnerBudget.product family78 8
    (HalfDomain.ofSpec family78 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family78 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain78_1024 : CertifiedDomain family78 :=
  OwnerBudget.product family78 1024
    (HalfDomain.ofSpec family78 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family78 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain78_2048 : CertifiedDomain family78 :=
  CertifiedDomain.ofCombined family78 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain78_4096 : CertifiedDomain family78 :=
  CertifiedDomain.ofCombined family78 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain78_8448 : CertifiedDomain family78 :=
  OwnerBudget.product family78 8448
    (HalfDomain.ofSpec family78 singleSpec72 0 singleSpec72_checked (by decide +kernel))
    (HalfDomain.ofSpec family78 singleSpec73 1 singleSpec73_checked (by decide +kernel))

def domain78_16384 : CertifiedDomain family78 :=
  CertifiedDomain.ofCombined family78 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain78_32768 : CertifiedDomain family78 :=
  CertifiedDomain.ofCombined family78 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains78 : List (CertifiedDomain family78) :=
  [domain78_1,domain78_2,domain78_4,domain78_8,domain78_4096,domain78_16384,domain78_32768,domain78_1024,domain78_2048,domain78_8448]

theorem domains78_members : ∀ d ∈ domains78, d.mask ∈ family78 := by decide +kernel
theorem domains78_distinct : domains78.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data78 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data78_checked : (data78).Check family78 := by decide +kernel

theorem forced78 (p : NormalizedPacking) (hf : codedMarkerFamily p = family78) :
    ∀ i, natCombinedOwners p (ownerIndex p (data78.masks i)) = data78.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains78 domains78_members domains78_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains78 domains78_members domains78_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains78 domains78_members domains78_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains78 domains78_members domains78_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case78_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family78) : False :=
  FourSquareCase.impossible data78 family78 data78_checked forced78 p hf

#print axioms case78_impossible
end N12Compact.FourSquareCases

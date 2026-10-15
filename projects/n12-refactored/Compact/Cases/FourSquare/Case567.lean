import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 567: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family567 : Finset Nat := {1,2,8,48,192,256,1024,2048,4096,8196,16384,32768}

def domain567_1 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain567_2 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain567_8 : CertifiedDomain family567 :=
  OwnerBudget.product family567 8
    (HalfDomain.ofSpec family567 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family567 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain567_256 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain567_1024 : CertifiedDomain family567 :=
  OwnerBudget.product family567 1024
    (HalfDomain.ofSpec family567 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family567 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain567_2048 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain567_4096 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain567_8196 : CertifiedDomain family567 :=
  OwnerBudget.product family567 8196
    (HalfDomain.ofSpec family567 singleSpec70 0 singleSpec70_checked (by decide +kernel))
    (HalfDomain.ofSeedHull family567 8196 1 5 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))

def domain567_16384 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain567_32768 : CertifiedDomain family567 :=
  CertifiedDomain.ofCombined family567 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains567 : List (CertifiedDomain family567) :=
  [domain567_1,domain567_2,domain567_8,domain567_8196,domain567_4096,domain567_16384,domain567_32768,domain567_256,domain567_1024,domain567_2048]

theorem domains567_members : ∀ d ∈ domains567, d.mask ∈ family567 := by decide +kernel
theorem domains567_distinct : domains567.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data567 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data567_checked : (data567).Check family567 := by decide +kernel

theorem forced567 (p : NormalizedPacking) (hf : codedMarkerFamily p = family567) :
    ∀ i, natCombinedOwners p (ownerIndex p (data567.masks i)) = data567.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains567 domains567_members domains567_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains567 domains567_members domains567_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains567 domains567_members domains567_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains567 domains567_members domains567_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case567_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family567) : False :=
  FourSquareCase.impossible data567 family567 data567_checked forced567 p hf

#print axioms case567_impossible
end N12Compact.FourSquareCases

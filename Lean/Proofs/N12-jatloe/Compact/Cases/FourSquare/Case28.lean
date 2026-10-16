import Compact.Bridge.FourSquareCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 28: compact shared four-square exclusion.
The numerical input archive supplies only the proposed point choices; the
ownership and all point memberships below are independently checked. -/
namespace N12Compact.FourSquareCases
open S12 OwnerBudget FourSquareCase
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family28 : Finset Nat := {1,2,4,8,48,192,256,1024,2048,4096,16384,32768}

def domain28_1 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain28_2 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain28_4 : CertifiedDomain family28 :=
  OwnerBudget.product family28 4
    (HalfDomain.ofSpec family28 singleSpec8 0 singleSpec8_checked (by decide +kernel))
    (HalfDomain.ofSpec family28 singleSpec10 1 singleSpec10_checked (by decide +kernel))

def domain28_8 : CertifiedDomain family28 :=
  OwnerBudget.product family28 8
    (HalfDomain.ofSpec family28 singleSpec11 0 singleSpec11_checked (by decide +kernel))
    (HalfDomain.ofSpec family28 singleSpec13 1 singleSpec13_checked (by decide +kernel))

def domain28_256 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain28_1024 : CertifiedDomain family28 :=
  OwnerBudget.product family28 1024
    (HalfDomain.ofSpec family28 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family28 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain28_2048 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain28_4096 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain28_16384 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain28_32768 : CertifiedDomain family28 :=
  CertifiedDomain.ofCombined family28 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains28 : List (CertifiedDomain family28) :=
  [domain28_1,domain28_2,domain28_4,domain28_8,domain28_4096,domain28_16384,domain28_32768,domain28_256,domain28_1024,domain28_2048]

theorem domains28_members : ∀ d ∈ domains28, d.mask ∈ family28 := by decide +kernel
theorem domains28_distinct : domains28.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data28 : FourSquareCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384],
    ![{5,16},{3,14},{1,11},{9,19}], 2, 8⟩

theorem data28_checked : (data28).Check family28 := by decide +kernel

theorem forced28 (p : NormalizedPacking) (hf : codedMarkerFamily p = family28) :
    ∀ i, natCombinedOwners p (ownerIndex p (data28.masks i)) = data28.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains28 domains28_members domains28_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains28 domains28_members domains28_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains28 domains28_members domains28_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains28 domains28_members domains28_distinct
      16384 {9,19} (by decide +kernel) p hf

theorem case28_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family28) : False :=
  FourSquareCase.impossible data28 family28 data28_checked forced28 p hf

#print axioms case28_impossible
end N12Compact.FourSquareCases

import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 992, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family992 : Finset Nat := {1,2,12,48,256,512,1024,2048,4288,8192,16384,32768}

def promotion992 : Promotion family992 :=
  ⟨4288, (by decide +kernel), (by intro k; fin_cases k <;> decide +kernel),
    (by intro k; fin_cases k <;> decide +kernel),
    (fun _ => 1), ![⟨(1,9/4),(1,11/4),(1,9/4),(1,113/50),1/50,0⟩,⟨(1,9/4),(1,11/4),(1,9/4),(1,12/5),3/10,0⟩],
    (by intro k; fin_cases k <;> decide +kernel)⟩

def domain992_1 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec0 combinedSpec0_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_2 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec2 combinedSpec2_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_256 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec5 combinedSpec5_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_512 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec7 combinedSpec7_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_1024 : CertifiedDomain family992 :=
  OwnerBudget.product family992 1024
    (promotion992.ofSpec singleSpec34 0 singleSpec34_checked (by rfl) (by rfl) (by rfl) (by decide +kernel))
    (promotion992.ofSpec singleSpec35 1 singleSpec35_checked (by rfl) (by rfl) (by rfl) (by decide +kernel))

def domain992_2048 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec12 combinedSpec12_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_4288 : CertifiedDomain family992 :=
  OwnerBudget.product family992 4288 (promotion992.ownDomain 0) (promotion992.ownDomain 1)

def domain992_8192 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec18 combinedSpec18_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_16384 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec20 combinedSpec20_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain992_32768 : CertifiedDomain family992 :=
  promotion992.combined combinedSpec22 combinedSpec22_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domains992 : List (CertifiedDomain family992) :=
  [domain992_1,domain992_2,domain992_4288,domain992_8192,domain992_16384,domain992_32768,domain992_256,domain992_512,domain992_1024,domain992_2048]

theorem domains992_members : ∀ d ∈ domains992, d.mask ∈ family992 := by decide +kernel
theorem domains992_distinct : domains992.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data992 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4288,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[⟨(1,9/4),(1,1543/500),(1,9/4),(1,12/5),75/418,0⟩],[],[]]⟩

theorem data992_checked : data992.Check family992 := by decide +kernel

theorem forced992 (p : NormalizedPacking) (hf : codedMarkerFamily p = family992) :
    ∀ i, natCombinedOwners p (ownerIndex p (data992.masks i)) = data992.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains992 domains992_members domains992_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains992 domains992_members domains992_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains992 domains992_members domains992_distinct
      4288 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains992 domains992_members domains992_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains992 domains992_members domains992_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case992_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family992) : False :=
  FourSquareConvexCase.impossible data992 family992 data992_checked forced992 p hf

#print axioms case992_impossible
end
end N12Compact.FourSquareConvexCases

import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.CornerPairDomain
import Compact.Bridge.UpperMidDomain
import Compact.Bridge.PromotedOwnerBudget
import S12.DomainSpecData

/-! Original marker case 1001, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareConvexCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family1001 : Finset Nat := {1,2,12,192,256,512,1024,2048,4096,8192,16384,32816}

def promotion1001 : Promotion family1001 :=
  ⟨32816, (by decide +kernel), (by intro k; fin_cases k <;> decide +kernel),
    (by intro k; fin_cases k <;> decide +kernel),
    (fun _ => 7), ![⟨(9/4,3),(11/4,3),(9/4,3),(12/5,3),3/10,0⟩,⟨(9/4,3),(11/4,3),(9/4,3),(113/50,3),1/50,0⟩],
    (by intro k; fin_cases k <;> decide +kernel)⟩

def domain1001_1 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec0 combinedSpec0_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_2 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec2 combinedSpec2_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_256 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec5 combinedSpec5_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_512 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec7 combinedSpec7_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_1024 : CertifiedDomain family1001 :=
  OwnerBudget.product family1001 1024
    (promotion1001.ofSpec singleSpec34 0 singleSpec34_checked (by rfl) (by rfl) (by rfl) (by decide +kernel))
    (promotion1001.ofSpec singleSpec35 1 singleSpec35_checked (by rfl) (by rfl) (by rfl) (by decide +kernel))

def domain1001_2048 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec12 combinedSpec12_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_4096 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec16 combinedSpec16_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_8192 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec18 combinedSpec18_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_16384 : CertifiedDomain family1001 :=
  promotion1001.combined combinedSpec20 combinedSpec20_checked
    (by rfl) (by rfl) (by rfl) (by rfl) (by decide +kernel) (by decide +kernel)

def domain1001_32816 : CertifiedDomain family1001 :=
  OwnerBudget.product family1001 32816 (promotion1001.ownDomain 0) (promotion1001.ownDomain 1)

def domains1001 : List (CertifiedDomain family1001) :=
  [domain1001_1,domain1001_2,domain1001_32816,domain1001_4096,domain1001_8192,domain1001_16384,domain1001_256,domain1001_512,domain1001_1024,domain1001_2048]

theorem domains1001_members : ∀ d ∈ domains1001, d.mask ∈ family1001 := by decide +kernel
theorem domains1001_distinct : domains1001.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data1001 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[],[]]⟩

theorem data1001_checked : data1001.Check family1001 := by decide +kernel

theorem forced1001 (p : NormalizedPacking) (hf : codedMarkerFamily p = family1001) :
    ∀ i, natCombinedOwners p (ownerIndex p (data1001.masks i)) = data1001.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains1001 domains1001_members domains1001_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains1001 domains1001_members domains1001_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains1001 domains1001_members domains1001_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains1001 domains1001_members domains1001_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains1001 domains1001_members domains1001_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case1001_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family1001) : False :=
  FourSquareConvexCase.impossible data1001 family1001 data1001_checked forced1001 p hf

#print axioms case1001_impossible
end
end N12Compact.FourSquareConvexCases

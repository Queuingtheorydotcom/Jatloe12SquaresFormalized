import Compact.Bridge.FourSquareConvexCase
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Original marker case 841, with exact auxiliary domains and convex point witnesses. -/
namespace N12Compact.FourSquareUnusedCases
open S12 OwnerBudget FourSquareConvexCase
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family841 : Finset Nat := {1,2,12,16,192,256,512,1024,2048,4096,8192,16384}

def domain841_1 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain841_2 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain841_16 : CertifiedDomain family841 :=
  OwnerBudget.product family841 16
    (HalfDomain.ofSpec family841 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family841 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain841_256 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain841_512 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain841_1024 : CertifiedDomain family841 :=
  OwnerBudget.product family841 1024
    (HalfDomain.ofSpec family841 singleSpec34 0 singleSpec34_checked (by decide +kernel))
    (HalfDomain.ofSpec family841 singleSpec35 1 singleSpec35_checked (by decide +kernel))

def domain841_2048 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain841_4096 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain841_8192 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain841_16384 : CertifiedDomain family841 :=
  CertifiedDomain.ofCombined family841 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domains841 : List (CertifiedDomain family841) :=
  [domain841_1,domain841_2,domain841_16,domain841_4096,domain841_8192,domain841_16384,domain841_256,domain841_512,domain841_1024,domain841_2048]

theorem domains841_members : ∀ d ∈ domains841, d.mask ∈ family841 := by decide +kernel
theorem domains841_distinct : domains841.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data841 : FourSquareConvexCase.Data :=
  ⟨⟨false,false,false⟩, ![1024,2048,4096,16384,512],
    ![{5,16},{3,14},{1,11},{9,19},{8,18}], 2,
    ![[],[],[],[],[]]⟩

theorem data841_checked : data841.Check family841 := by decide +kernel

theorem forced841 (p : NormalizedPacking) (hf : codedMarkerFamily p = family841) :
    ∀ i, natCombinedOwners p (ownerIndex p (data841.masks i)) = data841.owned i := by
  intro i
  fin_cases i
  · exact certified_domain_forced domains841 domains841_members domains841_distinct
      1024 {5,16} (by decide +kernel) p hf
  · exact certified_domain_forced domains841 domains841_members domains841_distinct
      2048 {3,14} (by decide +kernel) p hf
  · exact certified_domain_forced domains841 domains841_members domains841_distinct
      4096 {1,11} (by decide +kernel) p hf
  · exact certified_domain_forced domains841 domains841_members domains841_distinct
      16384 {9,19} (by decide +kernel) p hf
  · exact certified_domain_forced domains841 domains841_members domains841_distinct
      512 {8,18} (by decide +kernel) p hf

theorem case841_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family841) : False :=
  FourSquareConvexCase.impossible data841 family841 data841_checked forced841 p hf

#print axioms case841_impossible
end
end N12Compact.FourSquareUnusedCases

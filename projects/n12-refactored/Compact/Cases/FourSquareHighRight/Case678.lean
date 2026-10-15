import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import Compact.Cases.FourSquareHighRight.Crossings
import S12.DomainEnumeration
import S12.DomainSpecData

/-! Original case 678: exhaustive ownership alternatives, then
the shared geometry or a strict segment crossing. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family678 : Finset Nat := {1,2,12,16,32,192,256,512,2048,4096,8192,17408}

def domain678_1 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain678_2 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain678_16 : CertifiedDomain family678 :=
  OwnerBudget.product family678 16
    (HalfDomain.ofSpec family678 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family678 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain678_32 : CertifiedDomain family678 :=
  OwnerBudget.product family678 32
    (HalfDomain.ofSpec family678 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family678 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain678_256 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain678_512 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain678_2048 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain678_4096 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain678_8192 : CertifiedDomain family678 :=
  CertifiedDomain.ofCombined family678 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain678_17408 : CertifiedDomain family678 :=
  OwnerBudget.product family678 17408
    (HalfDomain.ofSpec family678 singleSpec87 0 singleSpec87_checked (by decide +kernel))
    (HalfDomain.singleton family678 17408 1 (by decide +kernel) (by decide +kernel))

def domains678 : List (CertifiedDomain family678) :=
  [domain678_1,domain678_2,domain678_16,domain678_32,domain678_4096,domain678_8192,domain678_256,domain678_512,domain678_2048,domain678_17408]

theorem domains678_members : ∀ d ∈ domains678, d.mask ∈ family678 := by decide +kernel
theorem domains678_distinct : domains678.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data678 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![17408,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data678_checked : data678.Check family678 := by decide +kernel

def assignments678 : List (List (Finset Nat)) :=
  [[{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,16},{3,14},{5,18}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,18},{3,14},{5,16}]]

theorem assignments678_checked : DomainCasesCheck domains678 assignments678 := by decide +kernel

theorem case678_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family678) : False := by
  have h := domain_cases_sound domains678 domains678_members domains678_distinct
    assignments678 assignments678_checked p hf
  simp only [assignments678, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1
  · apply OwnerSegmentCrossing.impossible crossing0 crossing0_inputs crossing0_checked
      family678 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h0
      change natCombinedOwners p (ownerIndex p 512) = {8,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h0
      change natCombinedOwners p (ownerIndex p 17408) = {5,18} at hh
      exact hh
  · apply FourSquareCaseHighRight.impossible_of_owned data678 family678
      data678_checked p hf
    intro i
    fin_cases i
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h1
      change natCombinedOwners p (ownerIndex p 17408) = {5,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h1
      change natCombinedOwners p (ownerIndex p 512) = {8,18} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[5]!) h1
      change natCombinedOwners p (ownerIndex p 8192) = {6,15} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[2]!) h1
      change natCombinedOwners p (ownerIndex p 16) = {7,17} at hh
      exact hh

#print axioms case678_impossible
end N12Compact.FourSquareHighRightCases

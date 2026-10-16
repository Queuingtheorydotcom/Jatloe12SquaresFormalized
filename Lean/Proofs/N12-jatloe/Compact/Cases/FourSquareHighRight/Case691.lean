import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import Compact.Cases.FourSquareHighRight.Crossings
import S12.DomainEnumeration
import S12.DomainSpecData

/-! Original case 691: exhaustive ownership alternatives, then
the shared geometry or a strict segment crossing. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family691 : Finset Nat := {1,2,12,16,32,192,256,512,4096,8192,17408,34816}

def domain691_1 : CertifiedDomain family691 :=
  CertifiedDomain.ofCombined family691 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain691_2 : CertifiedDomain family691 :=
  CertifiedDomain.ofCombined family691 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain691_16 : CertifiedDomain family691 :=
  OwnerBudget.product family691 16
    (HalfDomain.ofSpec family691 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family691 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain691_32 : CertifiedDomain family691 :=
  OwnerBudget.product family691 32
    (HalfDomain.ofSpec family691 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family691 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain691_256 : CertifiedDomain family691 :=
  CertifiedDomain.ofCombined family691 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain691_512 : CertifiedDomain family691 :=
  CertifiedDomain.ofCombined family691 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain691_4096 : CertifiedDomain family691 :=
  CertifiedDomain.ofCombined family691 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain691_8192 : CertifiedDomain family691 :=
  CertifiedDomain.ofCombined family691 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain691_17408 : CertifiedDomain family691 :=
  OwnerBudget.product family691 17408
    (HalfDomain.ofSpec family691 singleSpec87 0 singleSpec87_checked (by decide +kernel))
    (HalfDomain.singleton family691 17408 1 (by decide +kernel) (by decide +kernel))

def domain691_34816 : CertifiedDomain family691 :=
  OwnerBudget.product family691 34816
    (HalfDomain.singleton family691 34816 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.singleton family691 34816 1 (by decide +kernel) (by decide +kernel))

def domains691 : List (CertifiedDomain family691) :=
  [domain691_1,domain691_2,domain691_16,domain691_32,domain691_4096,domain691_8192,domain691_256,domain691_512,domain691_17408,domain691_34816]

theorem domains691_members : ∀ d ∈ domains691, d.mask ∈ family691 := by decide +kernel
theorem domains691_distinct : domains691.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data691 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![17408,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data691_checked : data691.Check family691 := by decide +kernel

def assignments691 : List (List (Finset Nat)) :=
  [[{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,16},{5,14},{3,18}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,16},{5,18},{3,14}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,18},{5,14},{3,16}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,18},{5,16},{3,14}]]

theorem assignments691_checked : DomainCasesCheck domains691 assignments691 := by decide +kernel

theorem case691_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family691) : False := by
  have h := domain_cases_sound domains691 domains691_members domains691_distinct
    assignments691 assignments691_checked p hf
  simp only [assignments691, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3
  · apply OwnerSegmentCrossing.impossible crossing2 crossing2_inputs crossing2_checked
      family691 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h0
      change natCombinedOwners p (ownerIndex p 512) = {8,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h0
      change natCombinedOwners p (ownerIndex p 34816) = {3,18} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing0 crossing0_inputs crossing0_checked
      family691 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h1
      change natCombinedOwners p (ownerIndex p 512) = {8,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h1
      change natCombinedOwners p (ownerIndex p 17408) = {5,18} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing3 crossing3_inputs crossing3_checked
      family691 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h2
      change natCombinedOwners p (ownerIndex p 17408) = {5,14} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h2
      change natCombinedOwners p (ownerIndex p 34816) = {3,16} at hh
      exact hh
  · apply FourSquareCaseHighRight.impossible_of_owned data691 family691
      data691_checked p hf
    intro i
    fin_cases i
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h3
      change natCombinedOwners p (ownerIndex p 17408) = {5,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h3
      change natCombinedOwners p (ownerIndex p 512) = {8,18} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[5]!) h3
      change natCombinedOwners p (ownerIndex p 8192) = {6,15} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[2]!) h3
      change natCombinedOwners p (ownerIndex p 16) = {7,17} at hh
      exact hh

#print axioms case691_impossible
end N12Compact.FourSquareHighRightCases

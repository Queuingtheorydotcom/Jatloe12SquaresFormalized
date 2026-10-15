import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import Compact.Cases.FourSquareHighRight.Crossings
import S12.DomainEnumeration
import S12.DomainSpecData

/-! Original case 694: exhaustive ownership alternatives, then
the shared geometry or a strict segment crossing. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family694 : Finset Nat := {1,2,12,16,32,192,256,512,6144,8192,17408,32768}

def domain694_1 : CertifiedDomain family694 :=
  CertifiedDomain.ofCombined family694 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain694_2 : CertifiedDomain family694 :=
  CertifiedDomain.ofCombined family694 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain694_16 : CertifiedDomain family694 :=
  OwnerBudget.product family694 16
    (HalfDomain.ofSpec family694 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family694 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain694_32 : CertifiedDomain family694 :=
  OwnerBudget.product family694 32
    (HalfDomain.ofSpec family694 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family694 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain694_256 : CertifiedDomain family694 :=
  CertifiedDomain.ofCombined family694 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain694_512 : CertifiedDomain family694 :=
  CertifiedDomain.ofCombined family694 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain694_6144 : CertifiedDomain family694 :=
  OwnerBudget.product family694 6144
    (HalfDomain.singleton family694 6144 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.singleton family694 6144 1 (by decide +kernel) (by decide +kernel))

def domain694_8192 : CertifiedDomain family694 :=
  CertifiedDomain.ofCombined family694 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain694_17408 : CertifiedDomain family694 :=
  OwnerBudget.product family694 17408
    (HalfDomain.ofSpec family694 singleSpec87 0 singleSpec87_checked (by decide +kernel))
    (HalfDomain.singleton family694 17408 1 (by decide +kernel) (by decide +kernel))

def domain694_32768 : CertifiedDomain family694 :=
  CertifiedDomain.ofCombined family694 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domains694 : List (CertifiedDomain family694) :=
  [domain694_1,domain694_2,domain694_16,domain694_32,domain694_8192,domain694_32768,domain694_256,domain694_512,domain694_17408,domain694_6144]

theorem domains694_members : ∀ d ∈ domains694, d.mask ∈ family694 := by decide +kernel
theorem domains694_distinct : domains694.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data694 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![17408,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data694_checked : data694.Check family694 := by decide +kernel

def assignments694 : List (List (Finset Nat)) :=
  [[{2,12},{0,10},{7,17},{9,19},{6,15},{3,14},{4,13},{8,16},{5,11},{1,18}],
   [{2,12},{0,10},{7,17},{9,19},{6,15},{3,14},{4,13},{8,16},{5,18},{1,11}],
   [{2,12},{0,10},{7,17},{9,19},{6,15},{3,14},{4,13},{8,18},{5,11},{1,16}],
   [{2,12},{0,10},{7,17},{9,19},{6,15},{3,14},{4,13},{8,18},{5,16},{1,11}]]

theorem assignments694_checked : DomainCasesCheck domains694 assignments694 := by decide +kernel

theorem case694_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family694) : False := by
  have h := domain_cases_sound domains694 domains694_members domains694_distinct
    assignments694 assignments694_checked p hf
  simp only [assignments694, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3
  · apply OwnerSegmentCrossing.impossible crossing4 crossing4_inputs crossing4_checked
      family694 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[6]!) h0
      change natCombinedOwners p (ownerIndex p 256) = {4,13} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h0
      change natCombinedOwners p (ownerIndex p 6144) = {1,18} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing0 crossing0_inputs crossing0_checked
      family694 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h1
      change natCombinedOwners p (ownerIndex p 512) = {8,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h1
      change natCombinedOwners p (ownerIndex p 17408) = {5,18} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing5 crossing5_inputs crossing5_checked
      family694 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[6]!) h2
      change natCombinedOwners p (ownerIndex p 256) = {4,13} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h2
      change natCombinedOwners p (ownerIndex p 6144) = {1,16} at hh
      exact hh
  · apply FourSquareCaseHighRight.impossible_of_owned data694 family694
      data694_checked p hf
    intro i
    fin_cases i
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h3
      change natCombinedOwners p (ownerIndex p 17408) = {5,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h3
      change natCombinedOwners p (ownerIndex p 512) = {8,18} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[4]!) h3
      change natCombinedOwners p (ownerIndex p 8192) = {6,15} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[2]!) h3
      change natCombinedOwners p (ownerIndex p 16) = {7,17} at hh
      exact hh

#print axioms case694_impossible
end N12Compact.FourSquareHighRightCases

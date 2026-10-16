import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import Compact.Cases.FourSquareHighRight.Crossings
import S12.DomainEnumeration
import S12.DomainSpecData

/-! Original case 680: exhaustive ownership alternatives, then
the shared geometry or a strict segment crossing. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family680 : Finset Nat := {1,2,12,16,32,192,256,512,2048,4096,16384,33792}

def domain680_1 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain680_2 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain680_16 : CertifiedDomain family680 :=
  OwnerBudget.product family680 16
    (HalfDomain.ofSpec family680 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family680 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain680_32 : CertifiedDomain family680 :=
  OwnerBudget.product family680 32
    (HalfDomain.ofSpec family680 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family680 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain680_256 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain680_512 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain680_2048 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain680_4096 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain680_16384 : CertifiedDomain family680 :=
  CertifiedDomain.ofCombined family680 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain680_33792 : CertifiedDomain family680 :=
  OwnerBudget.product family680 33792
    (HalfDomain.singleton family680 33792 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSpec family680 singleSpec101 1 singleSpec101_checked (by decide +kernel))

def domains680 : List (CertifiedDomain family680) :=
  [domain680_1,domain680_2,domain680_16,domain680_32,domain680_4096,domain680_16384,domain680_256,domain680_512,domain680_2048,domain680_33792]

theorem domains680_members : ∀ d ∈ domains680, d.mask ∈ family680 := by decide +kernel
theorem domains680_distinct : domains680.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data680 : FourSquareCaseHighRight.Data :=
  ⟨⟨false,false,false⟩, ![33792,2048,4096,32],
    ![{5,16},{3,14},{1,11},{9,19}], 2⟩

theorem data680_checked : data680.Check family680 := by decide +kernel

def assignments680 : List (List (Finset Nat)) :=
  [[{2,12},{0,10},{7,17},{9,19},{1,11},{8,18},{4,13},{6,15},{3,14},{5,16}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{8,18},{4,13},{6,15},{5,14},{3,16}]]

theorem assignments680_checked : DomainCasesCheck domains680 assignments680 := by decide +kernel

theorem case680_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family680) : False := by
  have h := domain_cases_sound domains680 domains680_members domains680_distinct
    assignments680 assignments680_checked p hf
  simp only [assignments680, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1
  · apply FourSquareCaseHighRight.impossible_of_owned data680 family680
      data680_checked p hf
    intro i
    fin_cases i
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h0
      change natCombinedOwners p (ownerIndex p 33792) = {5,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h0
      change natCombinedOwners p (ownerIndex p 2048) = {3,14} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[4]!) h0
      change natCombinedOwners p (ownerIndex p 4096) = {1,11} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[3]!) h0
      change natCombinedOwners p (ownerIndex p 32) = {9,19} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing1 crossing1_inputs crossing1_checked
      family680 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h1
      change natCombinedOwners p (ownerIndex p 2048) = {5,14} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h1
      change natCombinedOwners p (ownerIndex p 33792) = {3,16} at hh
      exact hh

#print axioms case680_impossible
end N12Compact.FourSquareHighRightCases

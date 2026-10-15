import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import Compact.Cases.FourSquareHighRight.Crossings
import S12.DomainEnumeration
import S12.DomainSpecData

/-! Original case 711: exhaustive ownership alternatives, then
the shared geometry or a strict segment crossing. -/
namespace N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family711 : Finset Nat := {1,2,12,16,32,192,512,2048,4096,8448,16384,33792}

def domain711_1 : CertifiedDomain family711 :=
  CertifiedDomain.ofCombined family711 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain711_2 : CertifiedDomain family711 :=
  CertifiedDomain.ofCombined family711 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain711_16 : CertifiedDomain family711 :=
  OwnerBudget.product family711 16
    (HalfDomain.ofSpec family711 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family711 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain711_32 : CertifiedDomain family711 :=
  OwnerBudget.product family711 32
    (HalfDomain.ofSpec family711 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family711 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain711_512 : CertifiedDomain family711 :=
  CertifiedDomain.ofCombined family711 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain711_2048 : CertifiedDomain family711 :=
  CertifiedDomain.ofCombined family711 combinedSpec12 combinedSpec12_checked (by decide +kernel)

def domain711_4096 : CertifiedDomain family711 :=
  CertifiedDomain.ofCombined family711 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain711_8448 : CertifiedDomain family711 :=
  OwnerBudget.product family711 8448
    (HalfDomain.ofSpec family711 singleSpec72 0 singleSpec72_checked (by decide +kernel))
    (HalfDomain.ofSpec family711 singleSpec73 1 singleSpec73_checked (by decide +kernel))

def domain711_16384 : CertifiedDomain family711 :=
  CertifiedDomain.ofCombined family711 combinedSpec20 combinedSpec20_checked (by decide +kernel)

def domain711_33792 : CertifiedDomain family711 :=
  OwnerBudget.product family711 33792
    (HalfDomain.singleton family711 33792 0 (by decide +kernel) (by decide +kernel))
    (HalfDomain.ofSpec family711 singleSpec101 1 singleSpec101_checked (by decide +kernel))

def domains711 : List (CertifiedDomain family711) :=
  [domain711_1,domain711_2,domain711_16,domain711_32,domain711_4096,domain711_16384,domain711_512,domain711_2048,domain711_8448,domain711_33792]

theorem domains711_members : ∀ d ∈ domains711, d.mask ∈ family711 := by decide +kernel
theorem domains711_distinct : domains711.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data711 : FourSquareCaseHighRight.Data :=
  ⟨⟨false,false,false⟩, ![33792,2048,4096,32],
    ![{5,16},{3,14},{1,11},{9,19}], 2⟩

theorem data711_checked : data711.Check family711 := by decide +kernel

def assignments711 : List (List (Finset Nat)) :=
  [[{2,12},{0,10},{7,17},{9,19},{1,11},{8,18},{4,15},{3,14},{6,13},{5,16}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{8,18},{4,15},{5,14},{6,13},{3,16}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{8,18},{6,15},{3,14},{4,13},{5,16}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{8,18},{6,15},{5,14},{4,13},{3,16}]]

theorem assignments711_checked : DomainCasesCheck domains711 assignments711 := by decide +kernel

theorem case711_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family711) : False := by
  have h := domain_cases_sound domains711 domains711_members domains711_distinct
    assignments711 assignments711_checked p hf
  simp only [assignments711, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3
  · apply FourSquareCaseHighRight.impossible_of_owned data711 family711
      data711_checked p hf
    intro i
    fin_cases i
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h0
      change natCombinedOwners p (ownerIndex p 33792) = {5,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h0
      change natCombinedOwners p (ownerIndex p 2048) = {3,14} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[4]!) h0
      change natCombinedOwners p (ownerIndex p 4096) = {1,11} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[3]!) h0
      change natCombinedOwners p (ownerIndex p 32) = {9,19} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing6 crossing6_inputs crossing6_checked
      family711 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[6]!) h1
      change natCombinedOwners p (ownerIndex p 512) = {4,15} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[8]!) h1
      change natCombinedOwners p (ownerIndex p 8448) = {6,13} at hh
      exact hh
  · apply FourSquareCaseHighRight.impossible_of_owned data711 family711
      data711_checked p hf
    intro i
    fin_cases i
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h2
      change natCombinedOwners p (ownerIndex p 33792) = {5,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h2
      change natCombinedOwners p (ownerIndex p 2048) = {3,14} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[4]!) h2
      change natCombinedOwners p (ownerIndex p 4096) = {1,11} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[3]!) h2
      change natCombinedOwners p (ownerIndex p 32) = {9,19} at hh
      exact hh
  · apply OwnerSegmentCrossing.impossible crossing1 crossing1_inputs crossing1_checked
      family711 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h3
      change natCombinedOwners p (ownerIndex p 2048) = {5,14} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h3
      change natCombinedOwners p (ownerIndex p 33792) = {3,16} at hh
      exact hh

#print axioms case711_impossible
end N12Compact.FourSquareHighRightCases

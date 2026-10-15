import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.OwnerBudget
import Compact.Cases.FourSquareHighRight.Crossings
import S12.DomainEnumeration
import S12.DomainSpecData

/-! Original case 690: exhaustive ownership alternatives, then
the shared geometry or a strict segment crossing. -/
namespace N12Compact.FourSquareHighRightExtraCases
open N12Compact.FourSquareHighRightCases
open S12 OwnerBudget FourSquareCaseHighRight
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family690 : Finset Nat := {1,2,12,16,32,192,256,512,32768,4096,8192,17408}

def domain690_1 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec0 combinedSpec0_checked (by decide +kernel)

def domain690_2 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec2 combinedSpec2_checked (by decide +kernel)

def domain690_16 : CertifiedDomain family690 :=
  OwnerBudget.product family690 16
    (HalfDomain.ofSpec family690 singleSpec14 0 singleSpec14_checked (by decide +kernel))
    (HalfDomain.ofSpec family690 singleSpec16 1 singleSpec16_checked (by decide +kernel))

def domain690_32 : CertifiedDomain family690 :=
  OwnerBudget.product family690 32
    (HalfDomain.ofSpec family690 singleSpec17 0 singleSpec17_checked (by decide +kernel))
    (HalfDomain.ofSpec family690 singleSpec18 1 singleSpec18_checked (by decide +kernel))

def domain690_256 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec5 combinedSpec5_checked (by decide +kernel)

def domain690_512 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec7 combinedSpec7_checked (by decide +kernel)

def domain690_32768 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec22 combinedSpec22_checked (by decide +kernel)

def domain690_4096 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec16 combinedSpec16_checked (by decide +kernel)

def domain690_8192 : CertifiedDomain family690 :=
  CertifiedDomain.ofCombined family690 combinedSpec18 combinedSpec18_checked (by decide +kernel)

def domain690_17408 : CertifiedDomain family690 :=
  OwnerBudget.product family690 17408
    (HalfDomain.ofSpec family690 singleSpec87 0 singleSpec87_checked (by decide +kernel))
    (HalfDomain.singleton family690 17408 1 (by decide +kernel) (by decide +kernel))

def domains690 : List (CertifiedDomain family690) :=
  [domain690_1,domain690_2,domain690_16,domain690_32,domain690_4096,domain690_8192,domain690_256,domain690_512,domain690_32768,domain690_17408]

theorem domains690_members : ∀ d ∈ domains690, d.mask ∈ family690 := by decide +kernel
theorem domains690_distinct : domains690.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def data690 : FourSquareCaseHighRight.Data :=
  ⟨⟨true,false,false⟩, ![17408,512,8192,16],
    ![{5,16},{8,18},{6,15},{7,17}], 1⟩

theorem data690_checked : data690.Check family690 := by decide +kernel

def assignments690 : List (List (Finset Nat)) :=
  [[{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,16},{3,14},{5,18}],
   [{2,12},{0,10},{7,17},{9,19},{1,11},{6,15},{4,13},{8,18},{3,14},{5,16}]]

theorem assignments690_checked : DomainCasesCheck domains690 assignments690 := by decide +kernel

theorem case690_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family690) : False := by
  have h := domain_cases_sound domains690 domains690_members domains690_distinct
    assignments690 assignments690_checked p hf
  simp only [assignments690, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1
  · apply OwnerSegmentCrossing.impossible crossing0 crossing0_inputs crossing0_checked
      family690 (by decide +kernel) (by decide +kernel) p hf
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[7]!) h0
      change natCombinedOwners p (ownerIndex p 512) = {8,16} at hh
      exact hh
    · have hh := congrArg (fun xs : List (Finset Nat) => xs[9]!) h0
      change natCombinedOwners p (ownerIndex p 17408) = {5,18} at hh
      exact hh
  · apply FourSquareCaseHighRight.impossible_of_owned data690 family690
      data690_checked p hf
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

#print axioms case690_impossible
end N12Compact.FourSquareHighRightExtraCases

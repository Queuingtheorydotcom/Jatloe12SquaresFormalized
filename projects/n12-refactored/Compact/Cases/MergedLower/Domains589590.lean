import Compact.Cases.MergedLower.Helpers

/-! Actual packing ownership entrances for the two merged lower-marker cases.
The selected nine domains are sufficient for the finite template proof;
the other three owners remain part of the original normalized packing. -/

namespace N12Compact.MergedLower
open S12 OwnerBudget RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family589 : Finset Nat :=
  {1,2,8,48,192,768,1024,2048,4096,8192,16384,32768}

def family590 : Finset Nat :=
  {1,2,8,48,192,768,1024,2048,4096,8196,16384,32768}

def domain589_1 : CertifiedDomain family589 :=
  direct family589 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_2 : CertifiedDomain family589 :=
  direct family589 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_8 : CertifiedDomain family589 :=
  reflected family589 8 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_1024 : CertifiedDomain family589 :=
  reflected family589 1024 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_2048 : CertifiedDomain family589 :=
  direct family589 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_4096 : CertifiedDomain family589 :=
  direct family589 combinedSpec17 combinedSpec17_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_8192 : CertifiedDomain family589 :=
  direct family589 combinedSpec19 combinedSpec19_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_16384 : CertifiedDomain family589 :=
  direct family589 combinedSpec21 combinedSpec21_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain589_32768 : CertifiedDomain family589 :=
  direct family589 combinedSpec24 combinedSpec24_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domains589 : List (CertifiedDomain family589) :=
  [domain589_1,domain589_2,domain589_8,domain589_4096,domain589_8192,
    domain589_16384,domain589_32768,domain589_1024,domain589_2048]

theorem domains589_members : ∀ d ∈ domains589, d.mask ∈ family589 := by decide +kernel
theorem domains589_distinct : domains589.Pairwise (fun a b => a.mask ≠ b.mask) := by
  decide +kernel

def domain590_1 : CertifiedDomain family590 :=
  direct family590 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain590_2 : CertifiedDomain family590 :=
  direct family590 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain590_8 : CertifiedDomain family590 :=
  reflected family590 8 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain590_1024 : CertifiedDomain family590 :=
  reflected family590 1024 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain590_2048 : CertifiedDomain family590 :=
  direct family590 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain590_4096 : CertifiedDomain family590 :=
  direct family590 combinedSpec17 combinedSpec17_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- G has budget two here. The wall seed forces G5 but does not make G a
singleton; all nine possible additional G points are retained. -/
def domain590_8196 : CertifiedDomain family590 :=
  OwnerBudget.product family590 8196
    (ofSingle family590 singleSpec70 singleSpec70_checked 0
      (by decide +kernel) (by decide +kernel))
    (ofSmallBudgetWithSeed family590 8196 1 (by decide +kernel)
      5 (by decide +kernel)
      ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem domain590_8196_allowed : domain590_8196.allowed =
    [{6,15},{6,10,15},{6,11,15},{6,12,15},{6,13,15},{6,14,15},
      {6,15,16},{6,15,17},{6,15,18},{6,15,19}] := by
  decide +kernel

def domain590_16384 : CertifiedDomain family590 :=
  direct family590 combinedSpec21 combinedSpec21_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain590_32768 : CertifiedDomain family590 :=
  direct family590 combinedSpec24 combinedSpec24_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domains590 : List (CertifiedDomain family590) :=
  [domain590_1,domain590_2,domain590_8,domain590_4096,domain590_8196,
    domain590_16384,domain590_32768,domain590_1024,domain590_2048]

theorem domains590_members : ∀ d ∈ domains590, d.mask ∈ family590 := by decide +kernel
theorem domains590_distinct : domains590.Pairwise (fun a b => a.mask ≠ b.mask) := by
  decide +kernel

end
end N12Compact.MergedLower

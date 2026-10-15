import Compact.Cases.MergedLower.Helpers

/-! Whole original families 71 and80. The selected nine domains retain every
possible packing but omit the merged lower square and both top corner pairs. -/
namespace N12Compact.MergedLower
open S12 RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family71 : Finset Nat := {1,2,4,8,48,192,768,1024,2048,4096,16384,32768}

def domain71_1 : CertifiedDomain family71 :=
  direct family71 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_2 : CertifiedDomain family71 :=
  direct family71 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_4 : CertifiedDomain family71 :=
  reflected family71 4 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_8 : CertifiedDomain family71 :=
  reflected family71 8 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_4096 : CertifiedDomain family71 :=
  direct family71 combinedSpec17 combinedSpec17_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_16384 : CertifiedDomain family71 :=
  direct family71 combinedSpec21 combinedSpec21_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_32768 : CertifiedDomain family71 :=
  direct family71 combinedSpec24 combinedSpec24_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_1024 : CertifiedDomain family71 :=
  reflected family71 1024 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain71_2048 : CertifiedDomain family71 :=
  direct family71 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domains71 : List (CertifiedDomain family71) :=
  [domain71_1,domain71_2,domain71_4,domain71_8,domain71_4096,domain71_16384,domain71_32768,domain71_1024,domain71_2048]

theorem domains71_members : ∀ d ∈ domains71, d.mask ∈ family71 := by decide +kernel
theorem domains71_distinct : domains71.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

def family80 : Finset Nat := {1,2,4,8,48,192,8960,1024,2048,4096,16384,32768}

def domain80_1 : CertifiedDomain family80 :=
  direct family80 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_2 : CertifiedDomain family80 :=
  direct family80 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_4 : CertifiedDomain family80 :=
  reflected family80 4 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_8 : CertifiedDomain family80 :=
  reflected family80 8 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_4096 : CertifiedDomain family80 :=
  direct family80 combinedSpec17 combinedSpec17_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_16384 : CertifiedDomain family80 :=
  direct family80 combinedSpec21 combinedSpec21_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_32768 : CertifiedDomain family80 :=
  direct family80 combinedSpec24 combinedSpec24_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_1024 : CertifiedDomain family80 :=
  reflected family80 1024 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain80_2048 : CertifiedDomain family80 :=
  direct family80 combinedSpec13 combinedSpec13_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domains80 : List (CertifiedDomain family80) :=
  [domain80_1,domain80_2,domain80_4,domain80_8,domain80_4096,domain80_16384,domain80_32768,domain80_1024,domain80_2048]

theorem domains80_members : ∀ d ∈ domains80, d.mask ∈ family80 := by decide +kernel
theorem domains80_distinct : domains80.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel

end
end N12Compact.MergedLower

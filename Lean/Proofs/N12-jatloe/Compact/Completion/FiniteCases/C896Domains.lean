import Compact.Completion.FiniteCases.C997Domains
import Compact.Completion.CommonCases.OriginalOwners

/-! The authentic F2/G3 census for original C896. Ordinary F owners
have one point, while their complete G sets may have two. The small
literal lists cache that exact F restriction after checked local geometry. -/
namespace N12Compact.FiniteCases.C896Domains
open S12 S12Pilot RelaxedOwnerDomain
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

def family : Finset Nat := {1,2,12,16,192,768,1024,2048,4096,8192,16384,32768}

private theorem f_count : (family∩auxExempt 0).card=2 := by decide +kernel
private theorem g_count : (family∩auxExempt 1).card=3 := by decide +kernel

private theorem bounds (mask : Nat) (w : SingleSpec) (k : Fin 2)
    (low : w.lower=1) (high : w.upper=2) (non : mask∉auxExempt k) :
    Bounds family mask w k := by
  unfold Bounds upper lower
  rw [low,high]
  simp only [non,ite_false]
  fin_cases k
  · change 1 ≤ 1 ∧ (family∩auxExempt 0).card - 2 + 1 ≤ 2
    rw [f_count]; norm_num
  · change 1 ≤ 1 ∧ (family∩auxExempt 1).card - 2 + 1 ≤ 2
    rw [g_count]; norm_num

private def restrict (d : CertifiedDomain family) (non : d.mask∉auxExempt 0) :=
  restrictFCardOne family d f_count non

def bottomAllowed : List (Finset Nat) :=
  [{2,12},{2,10,12},{2,12,15},{6,15},{6,12,15},{6,15,18}]
def bottom : CertifiedDomain family :=
  cached_domain _ (restrict (ofCombined _ combinedSpec19 combinedSpec19_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))) (by decide +kernel))
    8192 bottomAllowed rfl rfl

def leftAllowed : List (Finset Nat) := [{0,10},{0,10,13},{1,11},{1,11,13}]
def left : CertifiedDomain family :=
  cached_domain _ (restrict (ofCombined _ combinedSpec17 combinedSpec17_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))) (by decide +kernel))
    4096 leftAllowed rfl rfl

def topAllowed : List (Finset Nat) :=
  [{3,14},{3,11,14},{3,14,17},{7,17},{7,14,17},{7,17,19}]
def top : CertifiedDomain family :=
  cached_domain _ (restrict (ofCombined _ combinedSpec24 combinedSpec24_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))) (by decide +kernel))
    32768 topAllowed rfl rfl

def northwestAllowed : List (Finset Nat) :=
  [{1,11},{1,13},{1,14},{1,11,13},{1,11,14},{1,13,14},
    {3,11},{3,13},{3,14},{3,11,13},{3,11,14},{3,13,14},
    {5,11},{5,13},{5,14},{5,11,13},{5,11,14},{5,13,14},
    {5,13,16},{5,13,17},{5,14,16},{5,14,17}]
def northwest : CertifiedDomain family :=
  cached_domain _ (restrict (ofCombined _ combinedSpec13 combinedSpec13_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))) (by decide +kernel))
    2048 northwestAllowed rfl rfl

def rightAllowed : List (Finset Nat) := [{8,18},{8,16,18},{9,19},{9,16,19}]
def right : CertifiedDomain family :=
  cached_domain _ (restrict (ofCombined _ combinedSpec21 combinedSpec21_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))) (by decide +kernel))
    16384 rightAllowed rfl rfl

def northeastF : OwnerBudget.HalfDomain family 1024 0 :=
  ofSingle _ singleSpec34 singleSpec34_checked 0 (by decide +kernel) (by
    change 1≤lower 1024 0 ∧ upper family 1024 0≤1
    unfold upper lower
    rw [f_count]
    norm_num [show 1024∉auxExempt 0 by decide +kernel])

private theorem bottom_cut : ∀ s∈bottomAllowed, 2∉s → 6∈s ∧ 15∈s := by decide +kernel
private theorem left_cut : ∀ s∈leftAllowed, 0∉s → 1∈s ∧ 11∈s := by decide +kernel
private theorem top_cut : ∀ s∈topAllowed, 7∉s → 3∈s ∧ 14∈s := by decide +kernel
private theorem northwest_cut : ∀ s∈northwestAllowed,
    1∉s → 3∉s → 11∉s → 14∉s → 5∈s ∧ 13∈s := by decide +kernel
private theorem right_cut : ∀ s∈rightAllowed, 9∉s → 8∈s ∧ 18∈s := by decide +kernel

theorem bottom_forced (s : Finset Nat) (member : s∈bottomAllowed) (noTwo : 2∉s) :
    6∈s ∧ 15∈s := bottom_cut s member noTwo
theorem left_forced (s : Finset Nat) (member : s∈leftAllowed) (noZero : 0∉s) :
    1∈s ∧ 11∈s := left_cut s member noZero
theorem top_forced (s : Finset Nat) (member : s∈topAllowed) (noSeven : 7∉s) :
    3∈s ∧ 14∈s := top_cut s member noSeven
theorem northwest_forced (s : Finset Nat) (member : s∈northwestAllowed)
    (noOne : 1∉s) (noThree : 3∉s) (noEleven : 11∉s) (noFourteen : 14∉s) :
    5∈s ∧ 13∈s := northwest_cut s member noOne noThree noEleven noFourteen
theorem right_forced (s : Finset Nat) (member : s∈rightAllowed) (noNine : 9∉s) :
    8∈s ∧ 18∈s := right_cut s member noNine

#print axioms northwest
end
end N12Compact.FiniteCases.C896Domains

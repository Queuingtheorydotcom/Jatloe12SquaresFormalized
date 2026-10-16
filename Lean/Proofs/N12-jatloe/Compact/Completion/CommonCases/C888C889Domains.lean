import Compact.Completion.CommonCases.OriginalOwners
import S12.DomainSpecData

/-! Authentic C888/C889 domains with literal fields cached after the real
F3/G2 budget. Half-turn transport maps the 64 accepted combined owners
structurally, without regenerating the Cartesian product of half lists. -/
namespace N12Compact.CommonCases.C888C889
open S12 S12Pilot OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

def rightMask (b : Bool) : Nat := if b then 16416 else 16384
def family (b : Bool) : Finset Nat :=
  {1,2,12,16,192,512,1024,2304,4096,8192,rightMask b,32768}
private theorem budget_counts (b : Bool) :
    ((family b)∩auxExempt 0).card=3 ∧ ((family b)∩auxExempt 1).card=2 := by
  cases b <;> decide +kernel

private def direct (b : Bool) (w : CombinedSpec) (hw : w.Check)
    (first : Bounds (family b) w.mask w.first.val 0)
    (second : Bounds (family b) w.mask w.second.val 1)
    (fNon : w.mask∉auxExempt 0) (gNon : w.mask∉auxExempt 1) : CertifiedDomain (family b) :=
  restrict_budget23 (family b) (ofCombined (family b) w hw first second)
    (budget_counts b).1 (budget_counts b).2 fNon gNon
def southwestAllowed : List (Finset Nat) := [{2,12}]

def southwestDomain (b : Bool) : CertifiedDomain (family b) :=
  cached_domain (family b)
    (direct b combinedSpec1 combinedSpec1_checked
      (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    1 southwestAllowed rfl rfl

def singletonAllowed : List (Finset Nat) := [{7,17}]

def singletonDomain (b : Bool) : CertifiedDomain (family b) :=
  cached_domain (family b)
    (direct b combinedSpec4 combinedSpec4_checked
      (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    16 singletonAllowed rfl rfl

def bottomAllowed : List (Finset Nat) := [{2,12},{6,15},{2,4,12},{4,6,15}]

def bottomDomain (b : Bool) : CertifiedDomain (family b) :=
  cached_domain (family b)
    (direct b combinedSpec19 combinedSpec19_checked
      (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    8192 bottomAllowed rfl rfl

def southAllowed : List (Finset Nat) := [{4,15},{4,16},{4,18},{6,15},{6,16},{6,18},{8,15},{8,16},{8,18},{4,5,16},{4,6,15},{4,6,16},{4,6,18},{4,8,15},{4,8,16},{4,8,18},{4,9,16},{5,8,16},{6,8,15},{6,8,16},{6,8,18},{8,9,16}]

def southDomain (b : Bool) : CertifiedDomain (family b) :=
  cached_domain (family b)
    (direct b combinedSpec8 combinedSpec8_checked
      (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    512 southAllowed rfl rfl

def rightAllowed : List (Finset Nat) := [{8,18},{9,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19}]

def rightDomain : CertifiedDomain (family false) :=
  cached_domain (family false)
    (direct false combinedSpec21 combinedSpec21_checked
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    16384 rightAllowed rfl rfl

def northFullAllowed : List (Finset Nat) := [{9,19},{9,17},{9,16},{9,19,17},{9,19,16},{9,17,16},{7,19},{7,17},{7,16},{7,19,17},{7,19,16},{7,17,16},{5,19},{5,17},{5,16},{5,19,17},{5,19,16},{5,17,16},{5,17,14},{5,17,13},{5,16,14},{5,16,13},{9,8,16},{9,8,19,16},{9,8,18,16},{9,8,17,16},{9,7,19},{9,7,17},{9,7,16},{9,7,19,17},{9,7,19,16},{9,7,17,16},{9,5,19},{9,5,17},{9,5,16},{9,5,19,17},{9,5,19,16},{9,5,17,16},{9,5,17,14},{9,5,17,13},{9,5,16,14},{9,5,16,13},{9,4,16},{9,4,19,16},{9,4,17,16},{8,5,16},{8,5,17,16},{8,5,16,14},{8,5,16,13},{7,5,19},{7,5,17},{7,5,16},{7,5,19,17},{7,5,19,16},{7,5,17,16},{7,5,17,14},{7,5,17,13},{7,5,16,13},{5,4,16},{5,4,19,16},{5,4,17,16},{5,4,16,14},{5,4,16,13},{5,3,17,14}]

def northAllowed : List (Finset Nat) := [{9,19},{9,17},{9,16},{7,19},{7,17},{7,16},{5,19},{5,17},{5,16},{9,8,16},{9,7,19},{9,7,17},{9,7,16},{9,5,19},{9,5,17},{9,5,16},{9,4,16},{8,5,16},{7,5,19},{7,5,17},{7,5,16},{5,4,16}]

private def halfturnedCombined (s : Finset Nat) : Finset Nat :=
  combinedOwners (pushOwners halfTurnPerm (firstHalf s))
    (pushOwners halfTurnPerm ((secondHalf s).image (fun n => n-10)))

private theorem halfturned_combined (x y : Finset Nat) (hx : x⊆Finset.range 10) :
    halfturnedCombined (combinedOwners x y)=
      combinedOwners (pushOwners halfTurnPerm x) (pushOwners halfTurnPerm y) := by
  unfold halfturnedCombined
  rw [firstHalf_combined x y hx,secondHalf_combined x y hx]
  have inverse : (y.image (fun n => n+10)).image (fun n => n-10)=y := by
    simp only [Finset.image_image]
    simp [Function.comp_def]
  rw [inverse]

private theorem halfturned_checked :
    combinedSpec6.allowed.map halfturnedCombined=northFullAllowed := by decide +kernel

private theorem first_range : ∀ x∈combinedSpec6.first.val.allowed,
    x⊆Finset.range 10 := by decide +kernel

private theorem halfturned_included (x y : Finset Nat)
    (hx : x∈combinedSpec6.first.val.allowed)
    (_hy : y∈combinedSpec6.second.val.allowed)
    (hxy : combinedOwners x y∈combinedSpec6.allowed) :
    combinedOwners (pushOwners halfTurnPerm x) (pushOwners halfTurnPerm y)∈northFullAllowed := by
  rw [←halfturned_checked]
  exact List.mem_map.mpr ⟨combinedOwners x y,hxy,
    halfturned_combined x y (first_range x hx)⟩

def northDomain (b : Bool) : CertifiedDomain (family b) :=
  cached_domain (family b)
    (restrict_budget23 (family b)
      (ofTransformedCombined (family b) 1024 ⟨false,true,true⟩ (by decide +kernel)
        combinedSpec6 combinedSpec6_checked (by decide +kernel) (by decide +kernel)
        halfTurnPerm halfTurnPerm halfTurnF_points halfTurnG_points
        (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
        northFullAllowed (fun x hx y hy hxy => halfturned_included x y hx hy hxy))
      (budget_counts b).1 (budget_counts b).2
      (by change 1024∉auxExempt 0; decide +kernel)
      (by change 1024∉auxExempt 1; decide +kernel))
    1024 northAllowed rfl rfl

#print axioms northDomain
end
end N12Compact.CommonCases.C888C889

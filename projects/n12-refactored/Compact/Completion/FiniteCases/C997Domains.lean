import Compact.Completion.FiniteCases.C997Entrance
import Compact.Cases.MergedLower.Helpers

/-! Seven authentic C997 owner domains with one actual budget census and
small literal-list cuts. In particular both grids retain their genuine
three-exemption budgets: ordinary owners may own two points on each grid. -/
namespace N12Compact.FiniteCases.C997Domains
open S12 S12Pilot RelaxedOwnerDomain C997Entrance
noncomputable section
set_option Elab.async false

private theorem budget_count (k : Fin 2) : (family∩auxExempt k).card=3 := by
  fin_cases k <;> decide +kernel

private theorem ordinary_bounds (mask : Nat) (w : SingleSpec) (k : Fin 2)
    (low : w.lower=1) (high : w.upper=2) (non : mask∉auxExempt k) :
    Bounds family mask w k := by
  unfold Bounds upper lower
  rw [low,high,budget_count k]
  simp only [non,if_false]
  norm_num

private def cached (d : CertifiedDomain family) (mask : Nat)
    (allowed : List (Finset Nat)) (hm : d.mask=mask) (ha : d.allowed=allowed) :
    CertifiedDomain family :=
  ⟨mask,allowed,by
    intro p i hf hi
    rw [←ha]
    exact d.sound p i hf (hi.trans hm.symm)⟩

def southwestAllowed : List (Finset Nat) := [{2,12},{2,10,12}]

def southwest : CertifiedDomain family :=
  cached (ofCombined _ combinedSpec1 combinedSpec1_checked
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel)))
    _ southwestAllowed rfl rfl

def bottomAllowed : List (Finset Nat) := [{2,12},{2,10,12},{2,12,15},{6,15},{6,12,15},{6,15,18},{2,4,12},{2,4,12,15},{2,6,12,15},{4,6,15},{4,6,12,15}]

def bottom : CertifiedDomain family :=
  cached (ofCombined _ combinedSpec19 combinedSpec19_checked
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel)))
    _ bottomAllowed rfl rfl

def southwestCentralAllowed : List (Finset Nat) := [{0,10},{0,12},{0,13},{0,10,12},{0,10,13},{0,12,13},{2,10},{2,12},{2,13},{2,10,12},{2,10,13},{2,12,13},{4,10},{4,12},{4,13},{4,10,12},{4,10,13},{4,12,13},{4,12,15},{4,12,16},{4,13,15},{4,13,16},{0,1,13},{0,1,10,13},{0,1,11,13},{0,1,12,13},{0,2,10},{0,2,12},{0,2,13},{0,2,10,12},{0,2,10,13},{0,2,12,13},{0,4,10},{0,4,12},{0,4,13},{0,4,10,12},{0,4,10,13},{0,4,12,13},{0,4,12,15},{0,4,12,16},{0,4,13,15},{0,4,13,16},{0,5,13},{0,5,10,13},{0,5,12,13},{1,4,13},{1,4,12,13},{1,4,13,15},{1,4,13,16},{2,4,10},{2,4,12},{2,4,13},{2,4,10,12},{2,4,10,13},{2,4,12,13},{2,4,12,15},{2,4,12,16},{2,4,13,16},{4,5,13},{4,5,10,13},{4,5,12,13},{4,5,13,15},{4,5,13,16},{4,6,12,15}]

def southwestCentral : CertifiedDomain family :=
  cached (ofCombined _ combinedSpec6 combinedSpec6_checked
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel)))
    _ southwestCentralAllowed rfl rfl

def topAllowed : List (Finset Nat) := [{3,14},{3,11,14},{3,14,17},{7,17},{7,14,17},{7,17,19},{3,5,14},{3,5,14,17},{3,7,14,17},{5,7,17},{5,7,14,17}]

def top : CertifiedDomain family :=
  cached (ofCombined _ combinedSpec24 combinedSpec24_checked
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel)))
    _ topAllowed rfl rfl

def southeastAllowed : List (Finset Nat) := [{4,15},{4,16},{4,18},{4,12,15},{4,12,16},{4,13,15},{4,13,16},{4,15,16},{4,15,18},{4,16,18},{6,15},{6,16},{6,18},{6,15,16},{6,15,18},{6,16,18},{8,15},{8,16},{8,18},{8,15,16},{8,15,18},{8,16,18},{2,4,12,15},{4,5,16},{4,5,12,16},{4,5,13,16},{4,5,15,16},{4,5,16,18},{4,6,15},{4,6,16},{4,6,18},{4,6,12,15},{4,6,13,15},{4,6,13,16},{4,6,15,16},{4,6,15,18},{4,6,16,18},{4,8,15},{4,8,16},{4,8,18},{4,8,12,15},{4,8,12,16},{4,8,13,15},{4,8,13,16},{4,8,15,16},{4,8,15,18},{4,8,16,18},{4,9,16},{4,9,12,16},{4,9,13,16},{4,9,15,16},{5,8,16},{5,8,15,16},{5,8,16,18},{6,8,15},{6,8,16},{6,8,18},{6,8,15,16},{6,8,15,18},{6,8,16,18},{8,9,16},{8,9,15,16},{8,9,16,18},{8,9,16,19}]

def southeast : CertifiedDomain family :=
  cached (ofCombined _ combinedSpec8 combinedSpec8_checked
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel)))
    _ southeastAllowed rfl rfl

def rightAllowed : List (Finset Nat) := [{8,18},{8,16,18},{9,19},{9,16,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19}]

def right : CertifiedDomain family :=
  cached (ofCombined _ combinedSpec21 combinedSpec21_checked
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel)))
    _ rightAllowed rfl rfl

def northeastAllowed : List (Finset Nat) := [{9,19},{9,16},{9,17},{9,16,19},{9,17,19},{9,16,17},{7,19},{7,16},{7,17},{7,16,19},{7,17,19},{7,16,17},{5,19},{5,16},{5,17},{5,16,19},{5,17,19},{5,16,17},{5,13,16},{5,14,16},{5,13,17},{5,14,17},{8,9,16},{8,9,16,18},{8,9,16,19},{8,9,16,17},{5,8,16},{5,8,16,17},{5,8,13,16},{5,8,14,16},{7,9,19},{7,9,16},{7,9,17},{7,9,16,19},{7,9,17,19},{7,9,16,17},{4,9,16},{4,9,16,19},{4,9,16,17},{5,9,19},{5,9,16},{5,9,17},{5,9,16,19},{5,9,17,19},{5,9,16,17},{5,9,13,16},{5,9,14,16},{5,9,13,17},{5,9,14,17},{5,7,19},{5,7,16},{5,7,17},{5,7,16,19},{5,7,17,19},{5,7,16,17},{5,7,13,16},{5,7,13,17},{5,7,14,17},{4,5,16},{4,5,16,19},{4,5,16,17},{4,5,13,16},{4,5,14,16},{3,5,14,17}]

private def reflectedCombined (s : Finset Nat) : Finset Nat :=
  combinedOwners (pushOwners reflectXF (firstHalf s))
    (pushOwners reflectXG ((secondHalf s).image (fun n => n-10)))

private theorem reflected_combined (x y : Finset Nat) (hx : x⊆Finset.range 10) :
    reflectedCombined (combinedOwners x y)=
      combinedOwners (pushOwners reflectXF x) (pushOwners reflectXG y) := by
  unfold reflectedCombined
  rw [firstHalf_combined x y hx,secondHalf_combined x y hx]
  have inverse : (y.image (fun n => n+10)).image (fun n => n-10)=y := by
    simp only [Finset.image_image]
    simp [Function.comp_def]
  rw [inverse]

private theorem reflected_checked :
    combinedSpec13.allowed.map reflectedCombined=northeastAllowed := by decide +kernel

private theorem first_range : ∀ x∈combinedSpec13.first.val.allowed,
    x⊆Finset.range 10 := by decide +kernel

private theorem reflected_included (x y : Finset Nat)
    (hx : x∈combinedSpec13.first.val.allowed)
    (_hy : y∈combinedSpec13.second.val.allowed)
    (hxy : combinedOwners x y∈combinedSpec13.allowed) :
    combinedOwners (pushOwners reflectXF x) (pushOwners reflectXG y)∈northeastAllowed := by
  rw [←reflected_checked]
  exact List.mem_map.mpr ⟨combinedOwners x y,hxy,reflected_combined x y (first_range x hx)⟩

def northeast : CertifiedDomain family :=
  ofTransformedCombined _ 1024 ⟨false,true,false⟩ (by decide +kernel)
    combinedSpec13 combinedSpec13_checked (by decide +kernel) (by decide +kernel)
    reflectXF reflectXG reflectXF_points reflectXG_points
    (ordinary_bounds _ _ 0 rfl rfl (by decide +kernel))
    (ordinary_bounds _ _ 1 rfl rfl (by decide +kernel))
    northeastAllowed (fun x hx y hy hxy => reflected_included x y hx hy hxy)

#print axioms northeast
end
end N12Compact.FiniteCases.C997Domains

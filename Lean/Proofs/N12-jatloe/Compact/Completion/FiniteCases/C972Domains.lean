import Compact.Completion.FiniteCases.C975FiniteCuts

/-! Authentic C972 owner domains with its actual F3/G3 census. There
is no top-wall owner in this family. All two-point alternatives remain;
the northwest domain belongs to the actual marker-11 singleton. -/
namespace N12Compact.FiniteCases.C972Domains
open S12 S12Pilot RelaxedOwnerDomain
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

def family : Finset Nat := {1,2,12,48,192,256,512,1024,2048,4096,8192,16384}

private theorem count (k : Fin 2) : (family∩auxExempt k).card=3 := by
  fin_cases k <;> decide +kernel
private theorem bounds (mask : Nat) (w : SingleSpec) (k : Fin 2)
    (low : w.lower=1) (high : w.upper=2) (non : mask∉auxExempt k) :
    Bounds family mask w k := by
  unfold Bounds upper lower
  rw [low,high,count k]
  simp only [non,if_false]
  norm_num

def southwest : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec1 combinedSpec1_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    1 C997Domains.southwestAllowed rfl rfl
def leftSingleton : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec3 combinedSpec3_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    2 C975Domains.leftSingletonAllowed rfl rfl
def bottom : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec19 combinedSpec19_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    8192 C997Domains.bottomAllowed rfl rfl
def southwestCentral : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec6 combinedSpec6_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    256 C997Domains.southwestCentralAllowed rfl rfl
def left : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec17 combinedSpec17_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    4096 C975Domains.leftAllowed rfl rfl
def southeast : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec8 combinedSpec8_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    512 C997Domains.southeastAllowed rfl rfl
def right : CertifiedDomain family :=
  cached_domain _ (ofCombined _ combinedSpec21 combinedSpec21_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel)))
    16384 C997Domains.rightAllowed rfl rfl
def northwest : CertifiedDomain family :=
  ofCombined _ combinedSpec13 combinedSpec13_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))

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
    combinedSpec13.allowed.map reflectedCombined=C997Domains.northeastAllowed := by
  decide +kernel
private theorem first_range : ∀ x∈combinedSpec13.first.val.allowed,
    x⊆Finset.range 10 := by decide +kernel
private theorem reflected_included (x y : Finset Nat)
    (hx : x∈combinedSpec13.first.val.allowed)
    (_hy : y∈combinedSpec13.second.val.allowed)
    (hxy : combinedOwners x y∈combinedSpec13.allowed) :
    combinedOwners (pushOwners reflectXF x) (pushOwners reflectXG y)∈
      C997Domains.northeastAllowed := by
  rw [←reflected_checked]
  exact List.mem_map.mpr ⟨combinedOwners x y,hxy,reflected_combined x y (first_range x hx)⟩
def northeast : CertifiedDomain family :=
  ofTransformedCombined _ 1024 ⟨false,true,false⟩ (by decide +kernel)
    combinedSpec13 combinedSpec13_checked (by decide +kernel) (by decide +kernel)
    reflectXF reflectXG reflectXF_points reflectXG_points
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))
    C997Domains.northeastAllowed (fun x hx y hy hxy => reflected_included x y hx hy hxy)

theorem northeast_cut : ∀ s∈C997Domains.northeastAllowed,
    9∉s → 19∉s → (5∈s ∨ 7∈s) ∧ (16∈s ∨ 17∈s) := by decide +kernel

/-- After the actual singleton, wall, southwest and northeast points
are removed, G4 is forced in the actual northwest central square. -/
theorem northwest_cut : ∀ s∈combinedSpec13.allowed,
    0∉s → 1∉s → 4∉s → 7∉s → 10∉s → 11∉s → 13∉s → 17∉s →
      (3∈s ∨ 5∈s) ∧ 14∈s := by decide +kernel

#print axioms northeast
end
end N12Compact.FiniteCases.C972Domains

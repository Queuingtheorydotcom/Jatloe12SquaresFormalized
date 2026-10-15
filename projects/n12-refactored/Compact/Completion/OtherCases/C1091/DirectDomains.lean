import Compact.Completion.OtherCases.C1091.OriginalData
import Compact.Cases.MergedLower.Helpers

/-! Existing local specifications instantiated with C1091's actual
3/3 exemption counts. The local cuts operate on each whole auxiliary set,
including extra points; no joint catalogue or another family's theorem
is assumed. There are no new numerical certificates or native sites. -/
namespace N12Compact.Completion.OtherCases.C1091.DirectDomains
open S12 S12Pilot RelaxedOwnerDomain OriginalData
set_option Elab.async false
noncomputable section

theorem exemption_count (k : Fin 2) : (family∩auxExempt k).card=3 := by
  fin_cases k <;> decide +kernel

private theorem bounds (mask : Nat) (w : SingleSpec) (k : Fin 2)
    (low : w.lower=1) (high : w.upper=2) (ordinary : mask∉auxExempt k) :
    Bounds family mask w k := by
  unfold Bounds upper lower
  rw [low,high,exemption_count k]
  simp only [ordinary,if_false]
  norm_num

def northwest : CertifiedDomain family :=
  ofCombined family combinedSpec13 combinedSpec13_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))
def left : CertifiedDomain family :=
  ofCombined family combinedSpec17 combinedSpec17_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))
def bottom : CertifiedDomain family :=
  ofCombined family combinedSpec19 combinedSpec19_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))
def right : CertifiedDomain family :=
  ofCombined family combinedSpec21 combinedSpec21_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))
def top : CertifiedDomain family :=
  ofCombined family combinedSpec24 combinedSpec24_checked
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))

def northeast : CertifiedDomain family :=
  ofTransformedCombined family 1024 ⟨false,true,false⟩ (by decide +kernel)
    combinedSpec13 combinedSpec13_checked (by decide +kernel) (by decide +kernel)
    reflectXF reflectXG reflectXF_points reflectXG_points
    (bounds _ _ 0 rfl rfl (by decide +kernel))
    (bounds _ _ 1 rfl rfl (by decide +kernel))
    (MergedLower.reflectedAllowed combinedSpec13)
    (fun x hx y hy hxy => MergedLower.reflectedAllowed_mem _ _ _ hx hy hxy)

private theorem left_cut : ∀ owned∈combinedSpec17.allowed,0∉owned → 1∈owned ∧ 11∈owned :=
  by decide +kernel
private theorem bottom_cut : ∀ owned∈combinedSpec19.allowed,
    2∉owned → 4∉owned → 6∈owned := by decide +kernel
private theorem right_cut : ∀ owned∈combinedSpec21.allowed,9∉owned → 8∈owned ∧ 18∈owned :=
  by decide +kernel
private theorem top_cut : ∀ owned∈combinedSpec24.allowed,3∉owned → 7∈owned ∧ 17∈owned :=
  by decide +kernel
private theorem northwest_cut : ∀ owned∈combinedSpec13.allowed,
    11∉owned → 13∈owned ∨ 14∈owned := by decide +kernel
private theorem northeast_cut : ∀ owned∈MergedLower.reflectedAllowed combinedSpec13,
    16∉owned → 17∉owned → 19∈owned := by decide +kernel

theorem left_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mergedLow : (owners p 4).Inside 1 (87/50)) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5) := by
  have allowed := CommonCases.OriginalOwners.domain family left p hf (by decide +kernel)
  have absent : 0∉CommonCases.OriginalOwners.auxiliaries p 4096 := by
    intro member
    have own := (auxiliary p 8 0 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 8 4 (by decide) _ _ ⟨own,mergedLow⟩
  have pair := left_cut _ allowed absent
  have f := (auxiliary p 8 1 (by norm_num)).mpr pair.1
  have g := (auxiliary p 8 11 (by norm_num)).mpr pair.2
  norm_num [auxPoints,fPoints,gPoints] at f g
  exact ⟨f,g⟩

theorem bottom_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (southeast : (owners p 5).Inside 2 (87/50)) : (owners p 9).Inside (12/5) 1 := by
  have near := seed p hf 0 (28/25,1) (by decide +kernel)
  have far := seed p hf 0 (87/50,1) (by decide +kernel)
  norm_num at near far
  have singleton : (owners p 0).Inside (8/5) 1 :=
    CommonCases.OriginalOwners.horizontal_segment _ _ _ _ _ near far
      (by norm_num) (by norm_num) (by norm_num)
  have allowed := CommonCases.OriginalOwners.domain family bottom p hf (by decide +kernel)
  have absent2 : 2∉CommonCases.OriginalOwners.auxiliaries p 8192 := by
    intro member
    have own := (auxiliary p 9 2 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 9 0 (by decide) _ _ ⟨own,singleton⟩
  have absent4 : 4∉CommonCases.OriginalOwners.auxiliaries p 8192 := by
    intro member
    have own := (auxiliary p 9 4 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 9 5 (by decide) _ _ ⟨own,southeast⟩
  have own := (auxiliary p 9 6 (by norm_num)).mpr (bottom_cut _ allowed absent2 absent4)
  norm_num [auxPoints,fPoints,gPoints] at own
  exact own

theorem right_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (northeast : (owners p 6).Inside 3 (113/50)) :
    (owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5) := by
  have allowed := CommonCases.OriginalOwners.domain family right p hf (by decide +kernel)
  have absent : 9∉CommonCases.OriginalOwners.auxiliaries p 16384 := by
    intro member
    have own := (auxiliary p 10 9 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 10 6 (by decide) _ _ ⟨own,northeast⟩
  have pair := right_cut _ allowed absent
  have f := (auxiliary p 10 8 (by norm_num)).mpr pair.1
  have g := (auxiliary p 10 18 (by norm_num)).mpr pair.2
  norm_num [auxPoints,fPoints,gPoints] at f g
  exact ⟨f,g⟩

theorem top_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (northwest : (owners p 7).Inside (8/5) 3) :
    (owners p 11).Inside (12/5) 3 ∧ (owners p 11).Inside (113/50) 3 := by
  have allowed := CommonCases.OriginalOwners.domain family top p hf (by decide +kernel)
  have absent : 3∉CommonCases.OriginalOwners.auxiliaries p 32768 := by
    intro member
    have own := (auxiliary p 11 3 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 11 7 (by decide) _ _ ⟨own,northwest⟩
  have pair := top_cut _ allowed absent
  have f := (auxiliary p 11 7 (by norm_num)).mpr pair.1
  have g := (auxiliary p 11 17 (by norm_num)).mpr pair.2
  norm_num [auxPoints,fPoints,gPoints] at f g
  exact ⟨f,g⟩

theorem northwest_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (left : (owners p 8).Inside 1 (12/5)) :
    (owners p 7).Inside (87/50) 2 ∨ (owners p 7).Inside (87/50) 3 := by
  have allowed := CommonCases.OriginalOwners.domain family northwest p hf (by decide +kernel)
  have absent : 11∉CommonCases.OriginalOwners.auxiliaries p 2048 := by
    intro member
    have own := (auxiliary p 7 11 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 7 8 (by decide) _ _ ⟨own,left⟩
  rcases northwest_cut _ allowed absent with member | member
  · have own := (auxiliary p 7 13 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact Or.inl own
  · have own := (auxiliary p 7 14 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact Or.inr own

/-- The northeast G9 point needs no residual catalogue. Its other two
possible G arms are strict in the actual southeast and top squares. -/
theorem northeast_outer (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (southeast : (owners p 5).Inside (113/50) 2)
    (top : (owners p 11).Inside (113/50) 3) :
    (owners p 6).Inside 3 (12/5) := by
  have allowed := CommonCases.OriginalOwners.domain family northeast p hf (by decide +kernel)
  have absent16 : 16∉CommonCases.OriginalOwners.auxiliaries p 1024 := by
    intro member
    have own := (auxiliary p 6 16 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 6 5 (by decide) _ _ ⟨own,southeast⟩
  have absent17 : 17∉CommonCases.OriginalOwners.auxiliaries p 1024 := by
    intro member
    have own := (auxiliary p 6 17 (by norm_num)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at own
    exact apart p hf 6 11 (by decide) _ _ ⟨own,top⟩
  have own := (auxiliary p 6 19 (by norm_num)).mpr
    (northeast_cut _ allowed absent16 absent17)
  norm_num [auxPoints,fPoints,gPoints] at own
  exact own

end
#print axioms left_pair
#print axioms bottom_far
#print axioms right_pair
#print axioms top_pair
#print axioms northwest_cover
#print axioms northeast_outer
end N12Compact.Completion.OtherCases.C1091.DirectDomains

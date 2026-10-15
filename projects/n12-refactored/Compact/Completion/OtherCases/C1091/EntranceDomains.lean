import Compact.Completion.OtherCases.C1091.DirectDomains
import Compact.Completion.OtherCases.C1091.EntranceMergedLow
import Compact.Completion.OtherCases.C1089.ContinuousBottom

/-! C1091's actual three-exemption local domains, with complete owned
sets and extra ownership retained. Only the existing small domain tables
are inspected. In particular no exact256 certificate is applied to the
merged258 square, and no joint catalogue is asserted. Source only. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceDomains
open S12 S12Pilot RelaxedOwnerDomain OriginalData
set_option Elab.async false
noncomputable section

private theorem bounds (w : SingleSpec) (k : Fin 2)
    (low : w.lower=1) (high : w.upper=2) (ordinary : 512∉auxExempt k) :
    Bounds family 512 w k := by
  unfold Bounds upper lower
  rw [low,high,DirectDomains.exemption_count k]
  simp only [ordinary,if_false]
  norm_num

def southeast : CertifiedDomain family :=
  ofCombined family combinedSpec8 combinedSpec8_checked
    (bounds _ 0 rfl rfl (by decide +kernel))
    (bounds _ 1 rfl rfl (by decide +kernel))

private theorem cover (d : CertifiedDomain family) (i : Fin 12)
    (mask : d.mask=masks i) (a b c : Nat) (ha : a<20) (hb : b<20) (hc : c<20)
    (cut : ∀ s∈d.allowed,a∈s ∨ b∈s ∨ c∈s)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p i).Inside ((auxPoints 2)[a]!).1 ((auxPoints 2)[a]!).2 ∨
    (owners p i).Inside ((auxPoints 2)[b]!).1 ((auxPoints 2)[b]!).2 ∨
    (owners p i).Inside ((auxPoints 2)[c]!).1 ((auxPoints 2)[c]!).2 := by
  have allowed := CommonCases.OriginalOwners.domain family d p hf
    (by rw [mask]; exact member i)
  rw [mask] at allowed
  rcases cut _ allowed with own | own | own
  · exact Or.inl ((auxiliary p i a ha).mpr own)
  · exact Or.inr (Or.inl ((auxiliary p i b hb).mpr own))
  · exact Or.inr (Or.inr ((auxiliary p i c hc).mpr own))

theorem southeast_f (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 2 (87/50) ∨ (owners p 5).Inside (12/5) 1 ∨
      (owners p 5).Inside 3 (87/50) := by
  have h := cover southeast 5 rfl 4 6 8 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) p hf
  simpa [auxPoints,fPoints,gPoints] using h

theorem southeast_g (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside (113/50) 1 ∨ (owners p 5).Inside (113/50) 2 ∨
      (owners p 5).Inside 3 (8/5) := by
  have h := cover southeast 5 rfl 15 16 18 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) p hf
  simpa [auxPoints,fPoints,gPoints] using h

theorem northwest_f (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 1 (113/50) ∨ (owners p 7).Inside (8/5) 3 ∨
      (owners p 7).Inside 2 (113/50) := by
  have h := cover DirectDomains.northwest 7 rfl 1 3 5
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) p hf
  simpa [auxPoints,fPoints,gPoints] using h

theorem northwest_g (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 1 (12/5) ∨ (owners p 7).Inside (87/50) 2 ∨
      (owners p 7).Inside (87/50) 3 := by
  have h := cover DirectDomains.northwest 7 rfl 11 13 14
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) p hf
  simpa [auxPoints,fPoints,gPoints] using h

theorem northeast_f (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 2 (113/50) ∨ (owners p 6).Inside (12/5) 3 ∨
      (owners p 6).Inside 3 (113/50) := by
  have h := cover DirectDomains.northeast 6 rfl 5 7 9
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) p hf
  simpa [auxPoints,fPoints,gPoints] using h

theorem northeast_g (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (113/50) 2 ∨ (owners p 6).Inside (113/50) 3 ∨
      (owners p 6).Inside 3 (12/5) := by
  have h := cover DirectDomains.northeast 6 rfl 16 17 19
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) p hf
  simpa [auxPoints,fPoints,gPoints] using h

/-- The original Q0 owns G2. Every allowed bottom component avoiding
G2 contains F6, so the far bottom anchor is unconditional. -/
theorem bottom_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (12/5) 1 := by
  have singleton := seed p hf 0 (87/50,1) (by decide +kernel)
  norm_num at singleton
  have allowed := CommonCases.OriginalOwners.domain family DirectDomains.bottom p hf
    (by decide +kernel)
  have missing : 12∉CommonCases.OriginalOwners.auxiliaries p 8192 := by
    intro own
    have actual := (auxiliary p 9 12 (by norm_num)).mpr own
    norm_num [auxPoints,fPoints,gPoints] at actual
    exact apart p hf 9 0 (by decide) _ _ ⟨actual,singleton⟩
  have cut : ∀ row∈combinedSpec19.allowed,12∉row → 6∈row := by decide +kernel
  have actual := (auxiliary p 9 6 (by norm_num)).mpr (cut _ allowed missing)
  simpa [auxPoints,fPoints,gPoints] using actual

theorem bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    51/25<centerX (owners p 9) ∧ (owners p 9).Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → (owners p 9).Inside x 1 := by
  have marker := seed p hf 9 (2,457/500) (by decide +kernel)
  have singleton := seed p hf 0 (87/50,1) (by decide +kernel)
  have offRow := seed p hf 0 (187/100,19/25) (by decide +kernel)
  have central := seed p hf 5 (47/20,33/20) (by decide +kernel)
  norm_num at marker singleton offRow central
  exact C1089.ContinuousBottom.reach_of_far _ (side p 9) (box p 9)
    marker (bottom_far p hf)
    (fun own => apart p hf 9 0 (by decide) _ _ ⟨own,singleton⟩)
    (fun own => apart p hf 9 0 (by decide) _ _ ⟨own,offRow⟩)
    (fun own => apart p hf 9 5 (by decide) _ _ ⟨own,central⟩)

theorem left_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5) :=
  DirectDomains.left_pair p hf (EntranceMergedLow.original p hf)

theorem right_high_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 10).Inside 3 (87/50)) :
    (owners p 10).Inside 3 (113/50) ∧ (owners p 10).Inside 3 (12/5) := by
  have allowed := CommonCases.OriginalOwners.domain family DirectDomains.right p hf
    (by decide +kernel)
  have absent : 8∉CommonCases.OriginalOwners.auxiliaries p 16384 := by
    intro own
    have actual := (auxiliary p 10 8 (by norm_num)).mpr own
    exact missing (by simpa [auxPoints,fPoints,gPoints] using actual)
  have cut : ∀ row∈combinedSpec21.allowed,8∉row → 9∈row ∧ 19∈row := by decide +kernel
  have pair := cut _ allowed absent
  have a := (auxiliary p 10 9 (by norm_num)).mpr pair.1
  have b := (auxiliary p 10 19 (by norm_num)).mpr pair.2
  exact ⟨by simpa [auxPoints,fPoints,gPoints] using a,
    by simpa [auxPoints,fPoints,gPoints] using b⟩

theorem top_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 11).Inside (8/5) 3) : (owners p 11).Inside (12/5) 3 := by
  have allowed := CommonCases.OriginalOwners.domain family DirectDomains.top p hf
    (by decide +kernel)
  have absent : 3∉CommonCases.OriginalOwners.auxiliaries p 32768 := by
    intro own
    have actual := (auxiliary p 11 3 (by norm_num)).mpr own
    exact missing (by simpa [auxPoints,fPoints,gPoints] using actual)
  have cut : ∀ row∈combinedSpec24.allowed,3∉row → 7∈row := by decide +kernel
  have actual := (auxiliary p 11 7 (by norm_num)).mpr (cut _ allowed absent)
  simpa [auxPoints,fPoints,gPoints] using actual

theorem top_component (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (113/50) 3 ∨
      ((owners p 11).Inside (8/5) 3 ∧ (owners p 11).Inside (87/50) 3) := by
  have allowed := CommonCases.OriginalOwners.domain family DirectDomains.top p hf
    (by decide +kernel)
  have cut : ∀ row∈combinedSpec24.allowed,17∈row ∨ (3∈row ∧ 14∈row) := by
    decide +kernel
  rcases cut _ allowed with own|pair
  · left
    have actual := (auxiliary p 11 17 (by norm_num)).mpr own
    simpa [auxPoints,fPoints,gPoints] using actual
  · right
    have a := (auxiliary p 11 3 (by norm_num)).mpr pair.1
    have b := (auxiliary p 11 14 (by norm_num)).mpr pair.2
    exact ⟨by simpa [auxPoints,fPoints,gPoints] using a,
      by simpa [auxPoints,fPoints,gPoints] using b⟩

end
#print axioms southeast_f
#print axioms northeast_g
#print axioms bottom_bar
#print axioms left_pair
end N12Compact.Completion.OtherCases.C1091.EntranceDomains

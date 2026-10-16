import Compact.Completion.FiniteCases.C580581Entrance
import Compact.Cases.MergedLower.Helpers

/-! Compulsory F points for both original merged-left families. The ten
already derived G sets filter only authentic broad domains; foreign F
points are removed by the actual packing's strict owner disjointness. -/
namespace N12Compact.FiniteCases.C580581Points
open S12 S12Pilot RelaxedOwnerDomain C580581Entrance
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

private def southwest (v : Fin 2) : CertifiedDomain (family v) :=
  ofCombined _ combinedSpec1 combinedSpec1_checked
    (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
private def west (v : Fin 2) : CertifiedDomain (family v) :=
  ofCombined _ combinedSpec17 combinedSpec17_checked
    (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
private def south (v : Fin 2) : CertifiedDomain (family v) :=
  ofCombined _ combinedSpec8 combinedSpec8_checked
    (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
private def east (v : Fin 2) : CertifiedDomain (family v) :=
  ofCombined _ combinedSpec21 combinedSpec21_checked
    (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
private def north (v : Fin 2) : CertifiedDomain (family v) :=
  ofTransformedCombined _ 1024 ⟨false,true,false⟩ (by decide +kernel)
    combinedSpec13 combinedSpec13_checked (by decide +kernel) (by decide +kernel)
    reflectXF reflectXG reflectXF_points reflectXG_points
    (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
    (MergedLower.reflectedAllowed combinedSpec13)
    (fun x hx y hy hxy => MergedLower.reflectedAllowed_mem combinedSpec13 x y hx hy hxy)
private def upper (v : Fin 2) : CertifiedDomain (family v) :=
  ofCombined _ combinedSpec23 combinedSpec23_checked
    (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
private def lower (v : Fin 2) : CertifiedDomain (family v) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.elim0 j) i) v
  · exact ofCombined _ combinedSpec19 combinedSpec19_checked
      (by decide +kernel) (by decide +kernel)
  · exact OwnerBudget.product _ 8196
      (ofSmallBudgetWithSeed _ 8196 0 (by decide +kernel) 6 (by decide +kernel)
        ⟨(9/4,1),(11/4,1),(9/4,1),(12/5,1),3/10,0⟩
        (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (OwnerBudget.HalfDomain.ofSeedHull _ 8196 1 5 (by decide +kernel)
        (by decide +kernel) (by decide +kernel)
        ⟨(9/4,1),(11/4,1),(9/4,1),(113/50,1),1/50,0⟩
        (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel))

private theorem g_part (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (i : Fin 10) :
    secondHalf (auxiliaries p (claims v i).1)={(claims v i).2+10} := by
  unfold auxiliaries natCombinedOwners
  rw [secondHalf_combined _ _ (nat_aux_subset p 0 _)]
  change (G p (claims v i).1).image (fun n => n+10) = _
  rw [forced v p hf i]
  simp only [Finset.image_singleton]

private theorem foreign_aux (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (m n index : Nat)
    (hm : m∈family v) (hn : n∈family v) (different : m≠n)
    (owned : index∈auxiliaries p n) : index∉auxiliaries p m := by
  exact fun h => Finset.disjoint_left.mp
    (auxiliary_disjoint _ p hf m n hm hn different) h owned

theorem compulsory (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    2∈auxiliaries p 1 ∧ 0∈auxiliaries p 2 ∧ 8∈auxiliaries p 8 ∧
      6∈auxiliaries p (bottomMask v) ∧ 1∈auxiliaries p 4096 ∧
      4∈auxiliaries p 512 ∧ 9∈auxiliaries p 16384 ∧ 3∈auxiliaries p 32768 ∧
      (5∈auxiliaries p 1024 ∨ 7∈auxiliaries p 1024) := by
  have sw : 2∈auxiliaries p 1 := by
    have h := domain _ (southwest v) p hf (by fin_cases v <;> decide +kernel)
    have checked : ∀ v : Fin 2, ∀ s∈(southwest v).allowed, 2∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h
  have low : 0∈auxiliaries p 2 := by
    apply (auxiliary_exact p 2 0 (by norm_num)).mp
    have h := seed _ p hf 2 (by fin_cases v <;> decide +kernel)
      ((1,87/50) : ℚ×ℚ) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h ⊢
    exact h
  have se : 8∈auxiliaries p 8 := by
    apply (auxiliary_exact p 8 8 (by norm_num)).mp
    have h := seed _ p hf 8 (by fin_cases v <;> decide +kernel)
      ((3,87/50) : ℚ×ℚ) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h ⊢
    exact h
  have bottom : 6∈auxiliaries p (bottomMask v) := by
    have h := domain _ (lower v) p hf (by fin_cases v <;> decide +kernel)
    have mask : (lower v).mask=bottomMask v := by fin_cases v <;> decide +kernel
    rw [mask] at h
    have checked : ∀ v : Fin 2, ∀ s∈(lower v).allowed, secondHalf s={15} → 6∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h (by simpa [claims] using g_part v p hf 4)
  have left : 1∈auxiliaries p 4096 := by
    have h := domain _ (west v) p hf (by fin_cases v <;> decide +kernel)
    have checked : ∀ v : Fin 2, ∀ s∈(west v).allowed, secondHalf s={11} → 1∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h (by simpa [claims] using g_part v p hf 5)
  have right : 9∈auxiliaries p 16384 := by
    have h := domain _ (east v) p hf (by fin_cases v <;> decide +kernel)
    have checked : ∀ v : Fin 2, ∀ s∈(east v).allowed, secondHalf s={19} → 9∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h (by simpa [claims] using g_part v p hf 7)
  have top : 3∈auxiliaries p 32768 := by
    have h := domain _ (upper v) p hf (by fin_cases v <;> decide +kernel)
    have checked : ∀ v : Fin 2, ∀ s∈(upper v).allowed, secondHalf s={14} → 3∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h (by simpa [claims] using g_part v p hf 9)
  have south : 4∈auxiliaries p 512 := by
    have h := domain _ (south v) p hf (by fin_cases v <;> decide +kernel)
    have no6 := foreign_aux v p hf 512 (bottomMask v) 6
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) bottom
    have no8 := foreign_aux v p hf 512 8 8
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) se
    have checked : ∀ v : Fin 2, ∀ s∈(south v).allowed,
        secondHalf s={16} → 6∉s → 8∉s → 4∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h (by simpa [claims] using g_part v p hf 6) no6 no8
  have north : 5∈auxiliaries p 1024 ∨ 7∈auxiliaries p 1024 := by
    have h := domain _ (north v) p hf (by fin_cases v <;> decide +kernel)
    have no9 := foreign_aux v p hf 1024 16384 9
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) right
    have checked : ∀ v : Fin 2, ∀ s∈(north v).allowed,
        secondHalf s={17} → 9∉s → 5∈s ∨ 7∈s := by
      intro v; fin_cases v <;> decide +kernel
    exact checked v _ h (by simpa [claims] using g_part v p hf 8) no9
  exact ⟨sw,low,se,bottom,left,south,right,top,north⟩

#print axioms compulsory
end
end N12Compact.FiniteCases.C580581Points

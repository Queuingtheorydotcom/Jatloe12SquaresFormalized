import Compact.Completion.FiniteCases.C997Points
import Compact.Completion.CommonCases.CentralPair
import Compact.Assembly.RowIdentity

/-! Whole original C997 exclusion by one reflected continuous two-square
obstruction. The compulsory points are obtained from its true original
packing, and the advanced lower bar belongs to the actual bottom owner. -/
namespace N12Compact.FiniteCases.C997
open S12 S12Pilot S12Completion C997Entrance C997Points
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨bottomPoints,topPoints,sePoints,rightPoints,nePoints⟩ := compulsory p hf
  have own (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
      (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
    seed _ p hf mask member P checked
  have foreign (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
      (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun h => apart _ p hf m n hm hn different x y ⟨h,point⟩
  have markNE : (owner p 1024).Inside (47/20) (47/20) := by
    have h := own 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markSE : (owner p 512).Inside (47/20) (33/20) := by
    have h := own 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have neF : (owner p 1024).Inside 2 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 1024 5 (by norm_num) nePoints.1
  have neG : (owner p 1024).Inside (113/50) 2 := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 1024 16 (by norm_num) nePoints.2
  have seF : (owner p 512).Inside 3 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 512 8 (by norm_num) sePoints.1
  have seG : (owner p 512).Inside 3 (8/5) := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 512 18 (by norm_num) sePoints.2
  have bottomMarker : (owner p 8192).Inside 2 (457/500) := by
    have h := own 8192 (by decide +kernel) (2,457/500) (by decide +kernel)
    norm_num at h; exact h
  have bottomOuter : (owner p 8192).Inside (12/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 8192 6 (by norm_num) bottomPoints.1
  have bottomElbow : (owner p 8192).Inside (113/50) 1 := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 8192 15 (by norm_num) bottomPoints.2
  have topOuter : (owner p 32768).Inside (12/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 32768 7 (by norm_num) topPoints.1
  have swTip : (owner p 1).Inside (87/50) 1 := by
    have h := own 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have swSeed : (owner p 1).Inside (187/100) (19/25) := by
    have h := own 1 (by decide +kernel) (187/100,19/25) (by decide +kernel)
    norm_num at h; exact h
  have bottomFar : (owner p 8192).Inside (14/5) 1 := by
    have h := C981CompletionWallAdvance.point (pullSwap (owner p 8192)) (side p 8192)
      (container_pullSwap _ (box p 8192))
      ((inside_pullSwap _ _ _).mpr bottomMarker)
      ((inside_pullSwap _ _ _).mpr bottomOuter)
      (fun h => foreign 8192 1 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ swTip ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 8192 1 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ swSeed ((inside_pullSwap _ _ _).mp h))
      (fun h => foreign 8192 512 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ markSE ((inside_pullSwap _ _ _).mp h))
    exact (inside_pullSwap _ _ _).mp h
  have bottomBar (z : ℝ) (lo : 113/50≤z) (hi : z≤14/5) :
      (owner p 8192).Inside z 1 :=
    horizontal_segment _ _ _ _ _ bottomElbow bottomFar (by norm_num) lo hi
  have markNW : (owner p 2240).Inside (33/20) (47/20) := by
    have h := own 2240 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have rightMarker : (owner p 16384).Inside (1543/500) 2 := by
    have h := own 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have corner : (owner p 12).Inside 3 1 := by
    have h := own 12 (by decide +kernel) (3,1) (by decide +kernel)
    norm_num at h; exact h
  have cornerMarker : (owner p 12).Inside (1543/500) 1 := by
    have h := own 12 (by decide +kernel) (1543/500,1) (by decide +kernel)
    norm_num at h; exact h
  apply N12Compact.CommonCases.CentralPair.impossible
    (pullY (owner p 1024)) (pullY (owner p 512)) (side p 1024) (side p 512)
    (by norm_num [inside_pullY]; exact markNE)
    (by norm_num [inside_pullY]; exact neF)
    (by norm_num [inside_pullY]; exact neG)
    (by norm_num [inside_pullY]; exact (foreign 1024 2240 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ markNW))
    (by norm_num [inside_pullY]; exact (foreign 1024 32768 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ topOuter))
    (by norm_num [inside_pullY]; exact markSE)
    (Or.inr ⟨by norm_num [inside_pullY]; exact seF,
      by norm_num [inside_pullY]; exact seG⟩)
    (by norm_num [inside_pullY]; exact (foreign 512 16384 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ rightMarker))
    (by norm_num [inside_pullY]; exact (foreign 512 12 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ corner))
    (by norm_num [inside_pullY]; exact (foreign 512 12 (by decide +kernel)
      (by decide +kernel) (by decide +kernel) _ _ cornerMarker))
  · intro z lo hi own
    exact foreign 512 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ (bottomBar z lo hi) (by norm_num [inside_pullY] at own; exact own)
  · intro x y both
    exact apart _ p hf 1024 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _
      ⟨(inside_pullY _ _ _).mp both.1,(inside_pullY _ _ _).mp both.2⟩

private theorem row_checked :
    (RowIdentity.rowAt 528).originalId=997 ∧ (RowIdentity.rowAt 528).groups=family := by
  decide +kernel

/-- The unchanged original retained-row and arbitrary-real-packing contract. -/
theorem excludes : ExcludesCase 997 := by
  intro r hr he p hf
  exact family_impossible p (hf.trans (RowIdentity.family_at 528 997 family row_checked r hr he))

#print axioms family_impossible
#print axioms excludes
end
end N12Compact.FiniteCases.C997

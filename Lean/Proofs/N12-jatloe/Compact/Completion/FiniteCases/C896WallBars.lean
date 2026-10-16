import Compact.Completion.FiniteCases.C896Entrance
import Compact.Completion.C981.WallAdvance
import Compact.Geometry.WallUpperMissingReach

/-! Genuine wall segments after the original C896 entrance. The strong
left, bottom and top reaches use their actual foreign singleton seeds.
The right wall has only the weaker reach: no missing off-row seed is assumed. -/
namespace N12Compact.FiniteCases.C896WallBars
open S12 S12Pilot C896Domains
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

private theorem foreign_seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport n)) :
    ¬(owner p m).Inside P.1 P.2 :=
  fun h => apart _ p hf m n hm hn different _ _ ⟨h,seed _ p hf n hn P checked⟩

private theorem auxiliary (p : NormalizedPacking) (mask index : Nat) (bound : index<20)
    (owned : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr owned

theorem left_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 4096).Inside 1 (14/5) := by
  apply C981CompletionWallAdvance.point (owner p 4096) (side p 4096) (box p 4096)
  · have h := seed _ p hf 4096 (by decide +kernel) ((457/500,2) : ℚ×ℚ) (by decide +kernel)
    norm_num at h; exact h
  · have h := auxiliary p 4096 11 (by decide +kernel) (C896Entrance.compulsory p hf).leftWall.2
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  · have h := foreign_seed p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  · have h := foreign_seed p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (19/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  · have h := foreign_seed p hf 4096 2048 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h

theorem bottom_right (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 8192).Inside (14/5) 1 := by
  have answer : (pullSwap (owner p 8192)).Inside 1 (14/5) := by
    apply C981CompletionWallAdvance.point (pullSwap (owner p 8192)) (side p 8192)
      (container_pullSwap _ (box p 8192))
    · have h := seed _ p hf 8192 (by decide +kernel) ((2,457/500) : ℚ×ℚ) (by decide +kernel)
      norm_num at h
      simpa only [inside_pullSwap] using h
    · have h := auxiliary p 8192 6 (by decide +kernel) (C896Entrance.compulsory p hf).bottom.1
      norm_num [auxPoints,fPoints,gPoints] at h
      simpa only [inside_pullSwap] using h
    · have h := foreign_seed p hf 8192 1 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (87/50,1) (by decide +kernel)
      norm_num at h
      simpa only [inside_pullSwap] using h
    · have h := foreign_seed p hf 8192 1 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (187/100,19/25) (by decide +kernel)
      norm_num at h
      simpa only [inside_pullSwap] using h
    · have h := foreign_seed p hf 8192 768 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (47/20,33/20) (by decide +kernel)
      norm_num at h
      simpa only [inside_pullSwap] using h
  simpa only [inside_pullSwap] using answer

theorem top_left (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 32768).Inside (6/5) 3 := by
  have answer : (pullSwap (pullX (pullY (owner p 32768)))).Inside 1 (14/5) := by
    apply C981CompletionWallAdvance.point (pullSwap (pullX (pullY (owner p 32768)))) (side p 32768)
      (container_pullSwap _ (container_pullX _ (container_pullY _ (box p 32768))))
    · have h := seed _ p hf 32768 (by decide +kernel) ((2,1543/500) : ℚ×ℚ) (by decide +kernel)
      norm_num at h
      norm_num [inside_pullSwap,inside_pullX,inside_pullY]
      exact h
    · have h := auxiliary p 32768 3 (by decide +kernel) (C896Entrance.compulsory p hf).top.1
      norm_num [auxPoints,fPoints,gPoints] at h
      norm_num [inside_pullSwap,inside_pullX,inside_pullY]
      exact h
    · have h := foreign_seed p hf 32768 16 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (113/50,3) (by decide +kernel)
      norm_num at h
      norm_num [inside_pullSwap,inside_pullX,inside_pullY]
      exact h
    · have h := foreign_seed p hf 32768 16 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (213/100,81/25) (by decide +kernel)
      norm_num at h
      norm_num [inside_pullSwap,inside_pullX,inside_pullY]
      exact h
    · have h := foreign_seed p hf 32768 2048 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (33/20,47/20) (by decide +kernel)
      norm_num at h
      norm_num [inside_pullSwap,inside_pullX,inside_pullY]
      exact h
  norm_num [inside_pullSwap,inside_pullX,inside_pullY] at answer
  exact answer

theorem right_low (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 16384).Inside 3 (36/25) := by
  have answer : (pullX (pullY (owner p 16384))).Inside 1 (64/25) := by
    apply WallUpperMissingReach.point (pullX (pullY (owner p 16384))) (side p 16384)
      (container_pullX _ (container_pullY _ (box p 16384)))
    · have h := seed _ p hf 16384 (by decide +kernel) ((1543/500,2) : ℚ×ℚ) (by decide +kernel)
      norm_num at h
      norm_num [inside_pullX,inside_pullY]
      exact h
    · have h := auxiliary p 16384 18 (by decide +kernel) (C896Entrance.compulsory p hf).rightWall.2
      norm_num [auxPoints,fPoints,gPoints] at h
      norm_num [inside_pullX,inside_pullY]
      exact h
    · have h := auxiliary p 1024 9 (by decide +kernel) (C896Entrance.compulsory p hf).northeast
      norm_num [auxPoints,fPoints,gPoints] at h
      norm_num [inside_pullX,inside_pullY]
      intro own
      exact apart _ p hf 16384 1024 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨own,h⟩
    · have h := foreign_seed p hf 16384 768 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (47/20,33/20) (by decide +kernel)
      norm_num at h
      norm_num [inside_pullX,inside_pullY]
      exact h
  norm_num [inside_pullX,inside_pullY] at answer
  exact answer

structure Bars (p : NormalizedPacking) : Prop where
  left : ∀ y, 113/50≤y → y≤14/5 → (owner p 4096).Inside 1 y
  bottom : ∀ x, 113/50≤x → x≤14/5 → (owner p 8192).Inside x 1
  top : ∀ x, 6/5≤x → x≤87/50 → (owner p 32768).Inside x 3
  right : ∀ y, 36/25≤y → y≤87/50 → (owner p 16384).Inside 3 y

theorem bars (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Bars p := by
  have points := C896Entrance.compulsory p hf
  have left := auxiliary p 4096 1 (by decide +kernel) points.leftWall.1
  have bottom := auxiliary p 8192 15 (by decide +kernel) points.bottom.2
  have top := auxiliary p 32768 14 (by decide +kernel) points.top.2
  have right := auxiliary p 16384 8 (by decide +kernel) points.rightWall.1
  norm_num [auxPoints,fPoints,gPoints] at left bottom top right
  exact ⟨fun y lo hi => vertical_segment _ _ _ _ _ left (left_high p hf) (by norm_num) lo hi,
    fun x lo hi => horizontal_segment _ _ _ _ _ bottom (bottom_right p hf) (by norm_num) lo hi,
    fun x lo hi => horizontal_segment _ _ _ _ _ (top_left p hf) top (by norm_num) lo hi,
    fun y lo hi => vertical_segment _ _ _ _ _ (right_low p hf) right (by norm_num) lo hi⟩

#print axioms bars
end
end N12Compact.FiniteCases.C896WallBars

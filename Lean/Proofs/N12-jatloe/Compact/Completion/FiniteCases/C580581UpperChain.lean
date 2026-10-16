import Compact.Completion.FiniteCases.C580581PilotInputs
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Completion.OtherCases.TopOnlyExtension

/-! Additional actual-owner consequences for the two original merged-left
families. Both paired upper corners are used as their full genuine squares.
These are entrance deductions; the coupled case ending remains separate. -/
namespace N12Compact.FiniteCases.C580581UpperChain
open S12 S12Pilot C580581Entrance C580581Points
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
noncomputable section
set_option Elab.async false

private theorem seed_point (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (mask : Nat) (member : mask∈family v)
    (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport mask)) :
    (owner p mask).Inside P.1 P.2 := seed _ p hf mask member P checked

private theorem foreign (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) (m n : Nat)
    (hm : m∈family v) (hn : n∈family v) (different : m≠n)
    (x y : ℝ) (own : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun h => apart _ p hf m n hm hn different x y ⟨h,own⟩

theorem left_far (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 4096).Inside 1 (14/5) := by
  have markerL : (owner p 4096).Inside (457/500) 2 := by
    have h := seed_point v p hf 4096 (by fin_cases v <;> decide +kernel)
      (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  have highL : (owner p 4096).Inside 1 (12/5) := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 5
  have lowK : (owner p 2).Inside 1 (87/50) := by
    have h := seed_point v p hf 2 (by fin_cases v <;> decide +kernel)
      (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  have seedK : (owner p 2).Inside (19/25) (187/100) := by
    have h := seed_point v p hf 2 (by fin_cases v <;> decide +kernel)
      (19/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  have markerM : (owner p 2304).Inside (33/20) (47/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  exact C981CompletionWallAdvance.point (owner p 4096) (side p 4096)
    (box p 4096) markerL highL
    (foreign v p hf 4096 2 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ lowK)
    (foreign v p hf 4096 2 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ seedK)
    (foreign v p hf 4096 2304 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ markerM)

theorem top_origin (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 32768).Inside 2 3 := by
  obtain ⟨_,_,_,_,_,_,_,top,_⟩ := compulsory v p hf
  let B := pullY (owner p 32768)
  let K := pullY (owner p 192)
  have boxB := container_pullY _ (box p 32768)
  have boxK := container_pullY _ (box p 192)
  have marker : (owner p 32768).Inside 2 (1543/500) := by
    have h := seed_point v p hf 32768 (by fin_cases v <;> decide +kernel)
      (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have inner : (owner p 32768).Inside (8/5) 3 := by
    have h := (auxiliary_exact p 32768 3 (by norm_num)).mpr top
    simpa [auxPoints,fPoints,gPoints] using h
  have cornerMarker : (owner p 192).Inside 1 (1543/500) := by
    have h := seed_point v p hf 192 (by fin_cases v <;> decide +kernel)
      (1,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have cornerPoint : (owner p 192).Inside 1 3 := by
    have h := seed_point v p hf 192 (by fin_cases v <;> decide +kernel)
      (1,3) (by decide +kernel)
    norm_num at h; exact h
  have wallHigh : (owner p 4096).Inside 1 (12/5) := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 5
  have wallMiddle : (owner p 4096).Inside 1 (5/2) := by
    have h := horizontal_segment (pullSwap (owner p 4096)) (12/5) (14/5) 1 (5/2)
      ((inside_pullSwap _ _ _).mpr wallHigh)
      ((inside_pullSwap _ _ _).mpr (left_far v p hf))
      (by norm_num) (by norm_num) (by norm_num)
    exact (inside_pullSwap _ _ _).mp h
  have missing : ¬(owner p 192).Inside 1 (5/2) :=
    foreign v p hf 192 4096 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ wallMiddle
  have origin := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 32768) ((p.congruent _).trans (p.congruent _).symm)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num only [inside_pullY]; exact marker)
    (by dsimp only [B]; norm_num only [inside_pullY]; exact inner)
    (by dsimp only [K]; norm_num only [inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num only [inside_pullY]; exact cornerPoint)
    (by dsimp only [K]; norm_num only [inside_pullY]; exact missing)
    (by
      intro x y h
      have hK : (owner p 192).Inside x (4-y) :=
        (inside_pullY _ _ _).mp h.1
      have hB : (owner p 32768).Inside x (4-y) :=
        (inside_pullY _ _ _).mp h.2
      exact apart _ p hf 192 32768 (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ ⟨hK,hB⟩)
  dsimp only [B] at origin
  norm_num only [inside_pullY] at origin
  exact origin

theorem northeast_extension (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 1024).Inside (5/2) 3 := by
  have marker : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point v p hf 1024 (by fin_cases v <;> decide +kernel)
      (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  exact TopOnlyExtension.point_original (owner p 1024) (side p 1024)
    marker (C580581CentralEntrance.northeast_top v p hf).1
    (foreign v p hf 1024 2304 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      (C580581CentralEntrance.merged_inward v p hf))
    (foreign v p hf 1024 32768 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ (top_origin v p hf))
    (foreign v p hf 1024 512 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      (C580581PilotInputs.southeast_east v p hf))

theorem right_origin (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 16384).Inside 3 2 := by
  let B := pullSwap (pullY (pullX (owner p 16384)))
  let K := pullSwap (pullY (pullX (owner p 48)))
  have boxB := container_pullSwap _ (container_pullY _ (container_pullX _ (box p 16384)))
  have boxK := container_pullSwap _ (container_pullY _ (container_pullX _ (box p 48)))
  have marker : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed_point v p hf 16384 (by fin_cases v <;> decide +kernel)
      (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have inner : (owner p 16384).Inside 3 (12/5) := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 7
  have cornerMarker : (owner p 48).Inside (1543/500) 3 := by
    have h := seed_point v p hf 48 (by fin_cases v <;> decide +kernel)
      (1543/500,3) (by decide +kernel)
    norm_num at h; exact h
  have cornerPoint : (owner p 48).Inside 3 3 := by
    have h := seed_point v p hf 48 (by fin_cases v <;> decide +kernel)
      (3,3) (by decide +kernel)
    norm_num at h; exact h
  have missing : ¬(owner p 48).Inside (5/2) 3 :=
    foreign v p hf 48 1024 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      (northeast_extension v p hf)
  have origin := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 16384) ((p.congruent _).trans (p.congruent _).symm)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact marker)
    (by dsimp only [B]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact inner)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact cornerPoint)
    (by dsimp only [K]; norm_num only [inside_pullSwap,inside_pullY,inside_pullX]; exact missing)
    (by
      intro x y h
      have hK : (owner p 48).Inside (4-y) (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY,inside_pullX] using h.1
      have hB : (owner p 16384).Inside (4-y) (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY,inside_pullX] using h.2
      exact apart _ p hf 48 16384 (by fin_cases v <;> decide +kernel)
        (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ ⟨hK,hB⟩)
  dsimp only [B] at origin
  norm_num only [inside_pullSwap,inside_pullY,inside_pullX] at origin
  exact origin

#print axioms left_far
#print axioms top_origin
#print axioms northeast_extension
#print axioms right_origin
end
end N12Compact.FiniteCases.C580581UpperChain

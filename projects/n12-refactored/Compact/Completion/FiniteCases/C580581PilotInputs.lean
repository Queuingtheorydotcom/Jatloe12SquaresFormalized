import Compact.Completion.FiniteCases.C580581CentralEntrance
import Compact.Completion.C981.WallAdvance
import Compact.Completion.C981.Crosspoint

/-! Actual-family inputs for the bounded three-owner proposal. These
deductions do not use its result. Both original bottom masks and both
corner-ownership alternatives of the singleton are retained. -/
namespace N12Compact.FiniteCases.C580581PilotInputs
open S12 S12Pilot C580581Entrance C580581Points
open N12Compact.CommonCases.OriginalOwners
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

private theorem aux_inside (p : NormalizedPacking) (mask index : Nat)
    (bound : index<20) (own : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr own

theorem bottom_far (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p (bottomMask v)).Inside (14/5) 1 := by
  obtain ⟨_,_,_,bottom,_,_,_,_,_⟩ := compulsory v p hf
  have markerB : (owner p (bottomMask v)).Inside 2 (457/500) := by
    have h := seed_point v p hf (bottomMask v) (by fin_cases v <;> decide +kernel)
      (2,457/500) (by fin_cases v <;> decide +kernel)
    norm_num at h; exact h
  have highB : (owner p (bottomMask v)).Inside (12/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_inside p (bottomMask v) 6 (by norm_num) bottom
  have lowSW : (owner p 1).Inside (87/50) 1 := by
    have h := seed_point v p hf 1 (by fin_cases v <;> decide +kernel)
      (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have seedSW : (owner p 1).Inside (187/100) (19/25) := by
    have h := seed_point v p hf 1 (by fin_cases v <;> decide +kernel)
      (187/100,19/25) (by decide +kernel)
    norm_num at h; exact h
  have markerSE : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point v p hf 512 (by fin_cases v <;> decide +kernel)
      (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have h := C981CompletionWallAdvance.point (pullSwap (owner p (bottomMask v)))
    (side p (bottomMask v)) (container_pullSwap _ (box p (bottomMask v)))
    ((inside_pullSwap _ _ _).mpr markerB) ((inside_pullSwap _ _ _).mpr highB)
    (fun h => foreign v p hf (bottomMask v) 1
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ lowSW ((inside_pullSwap _ _ _).mp h))
    (fun h => foreign v p hf (bottomMask v) 1
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ seedSW ((inside_pullSwap _ _ _).mp h))
    (fun h => foreign v p hf (bottomMask v) 512
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ markerSE ((inside_pullSwap _ _ _).mp h))
  exact (inside_pullSwap _ _ _).mp h

theorem southeast_east (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) : (owner p 512).Inside (5/2) 2 := by
  obtain ⟨_,_,_,bottom,_,south,_,_,_⟩ := compulsory v p hf
  have markerA : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point v p hf 512 (by fin_cases v <;> decide +kernel)
      (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have inwardA : (owner p 512).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 512 4 (by norm_num) south
  have elbowA : (owner p 512).Inside (113/50) 2 := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 6
  have markerSW : (owner p 2304).Inside (33/20) (33/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markerNE : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point v p hf 1024 (by fin_cases v <;> decide +kernel)
      (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have lowB : (owner p (bottomMask v)).Inside (113/50) 1 := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 4
  have middleB : (owner p (bottomMask v)).Inside (12/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_inside p (bottomMask v) 6 (by norm_num) bottom
  have highB : (owner p (bottomMask v)).Inside (5/2) 1 :=
    horizontal_segment _ _ _ _ _ lowB (bottom_far v p hf)
      (by norm_num) (by norm_num) (by norm_num)
  have result := C981CompletionCrosspoint.point (pullSwap (pullY (owner p 512)))
    (side p 512)
    (by norm_num [inside_pullSwap,inside_pullY]; exact elbowA)
    (by norm_num [inside_pullSwap,inside_pullY]; exact inwardA)
    (by norm_num [inside_pullSwap,inside_pullY]; exact markerA)
    (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign v p hf 512 2304
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ markerSW))
    (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign v p hf 512 1024
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ markerNE))
    (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign v p hf 512 (bottomMask v)
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ middleB))
    (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign v p hf 512 (bottomMask v)
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ highB))
  norm_num [inside_pullSwap,inside_pullY] at result
  exact result

theorem southeast_missing_center (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) : ¬(owner p 512).Inside 2 2 :=
  foreign v p hf 512 2304 (by fin_cases v <;> decide +kernel)
    (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
    (C580581CentralEntrance.merged_center v p hf)

/-- The actual right-wall owner advances using the actual southeast
singleton and northeast central owner. No southeast corner ownership is
assumed, and the two original bottom masks remain unrestricted. -/
theorem right_far (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 16384).Inside 3 (14/5) := by
  have markerR : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed_point v p hf 16384 (by fin_cases v <;> decide +kernel)
      (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have highR : (owner p 16384).Inside 3 (12/5) := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 7
  have lowO : (owner p 8).Inside 3 (87/50) := by
    have h := seed_point v p hf 8 (by fin_cases v <;> decide +kernel)
      (3,87/50) (by decide +kernel)
    norm_num at h; exact h
  have seedO : (owner p 8).Inside (81/25) (187/100) := by
    have h := seed_point v p hf 8 (by fin_cases v <;> decide +kernel)
      (81/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  have markerN : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point v p hf 1024 (by fin_cases v <;> decide +kernel)
      (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have result := C981CompletionWallAdvance.point (pullX (owner p 16384))
    (side p 16384) (container_pullX _ (box p 16384))
    (by norm_num [inside_pullX]; exact markerR)
    (by norm_num [inside_pullX]; exact highR)
    (by norm_num [inside_pullX]; exact (foreign v p hf 16384 8
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ lowO))
    (by norm_num [inside_pullX]; exact (foreign v p hf 16384 8
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ seedO))
    (by norm_num [inside_pullX]; exact (foreign v p hf 16384 1024
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ markerN))
  norm_num [inside_pullX] at result
  exact result

#print axioms bottom_far
#print axioms southeast_east
#print axioms southeast_missing_center
#print axioms right_far
end
end N12Compact.FiniteCases.C580581PilotInputs

import Compact.Completion.FiniteCases.C580581Points
import Compact.Completion.CommonCases.SouthwestPoint
import Compact.Completion.CommonCases.MergedNearPoint
import Compact.Completion.FiniteCases.MergedLeftCenter

/-! The two actual central owners reduce to one incoming merged square and
one top-outward neighbor. The inward NE alternative is excluded by a common
strict point, with the true corner and wall owners supplying every absence.
This is a genuine entrance reduction, not yet a whole case ending. -/
namespace N12Compact.FiniteCases.C580581CentralEntrance
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

theorem southeast_near (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 512).Inside (41/20) (39/20) := by
  obtain ⟨_,_,_,bottom,_,south,_,_,_⟩ := compulsory v p hf
  have mark : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point v p hf 512 (by fin_cases v <;> decide +kernel)
      (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have inward : (owner p 512).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 512 4 (by norm_num) south
  have elbow : (owner p 512).Inside (113/50) 2 := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 6
  have cornerLo : (owner p 8).Inside 3 (28/25) := by
    have h := seed_point v p hf 8 (by fin_cases v <;> decide +kernel)
      (3,28/25) (by decide +kernel)
    norm_num at h; exact h
  have cornerHi : (owner p 8).Inside 3 (87/50) := by
    have h := seed_point v p hf 8 (by fin_cases v <;> decide +kernel)
      (3,87/50) (by decide +kernel)
    norm_num at h; exact h
  have cornerMid : (owner p 8).Inside 3 (33/20) := by
    have h := horizontal_segment (pullSwap (owner p 8)) (28/25) (87/50) 3 (33/20)
      ((inside_pullSwap _ _ _).mpr cornerLo) ((inside_pullSwap _ _ _).mpr cornerHi)
      (by norm_num) (by norm_num) (by norm_num)
    exact (inside_pullSwap _ _ _).mp h
  have bottomHi : (owner p (bottomMask v)).Inside (12/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using
      aux_inside p (bottomMask v) 6 (by norm_num) bottom
  have bottomLo : (owner p (bottomMask v)).Inside (113/50) 1 := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 4
  have bottomMid : (owner p (bottomMask v)).Inside (47/20) 1 :=
    horizontal_segment _ _ _ _ _ bottomLo bottomHi
      (by norm_num) (by norm_num) (by norm_num)
  have near := N12Compact.CommonCases.SouthwestPoint.point (pullX (owner p 512)) (side p 512)
    (by norm_num [inside_pullX]; exact mark)
    (by norm_num [inside_pullX]; exact inward)
    (by norm_num [inside_pullX]; exact elbow)
    (by norm_num [inside_pullX]; exact (foreign v p hf 512 8
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ cornerMid))
    (by norm_num [inside_pullX]; exact (foreign v p hf 512 (bottomMask v)
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ bottomLo))
    (by norm_num [inside_pullX]; exact (foreign v p hf 512 (bottomMask v)
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) _ _ bottomMid))
    (by norm_num [inside_pullX]; exact (foreign v p hf 512 8
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ cornerHi))
  norm_num [inside_pullX] at near
  exact near

/-- The actual merged owner must take F5. Its F-exempt status and possible
empty F-label are retained until this geometric contradiction removes them. -/
theorem merged_inward (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 2304).Inside 2 (113/50) := by
  obtain ⟨_,_,_,_,left,south,_,_,_⟩ := compulsory v p hf
  have markSW : (owner p 2304).Inside (33/20) (33/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markNW : (owner p 2304).Inside (33/20) (47/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have inwardSE : (owner p 512).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 512 4 (by norm_num) south
  have low : (owner p 2).Inside 1 (87/50) := by
    have h := seed_point v p hf 2 (by fin_cases v <;> decide +kernel)
      (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  have wallF : (owner p 4096).Inside 1 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 4096 1 (by norm_num) left
  have wallMarker : (owner p 4096).Inside (457/500) 2 := by
    have h := seed_point v p hf 4096 (by fin_cases v <;> decide +kernel)
      (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  by_contra missing
  have near := N12Compact.CommonCases.MergedNearPoint.points_original
    (pullX (owner p 2304)) (side p 2304)
    (by norm_num [inside_pullX]; exact markSW)
    (by norm_num [inside_pullX]; exact markNW)
    (by norm_num [inside_pullX]; exact (foreign v p hf 2304 512
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ inwardSE))
    (by norm_num [inside_pullX]; exact missing)
    (by norm_num [inside_pullX]; exact (foreign v p hf 2304 2
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ low))
    (by norm_num [inside_pullX]; exact (foreign v p hf 2304 4096
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ wallF))
    (by norm_num [inside_pullX]; exact (foreign v p hf 2304 4096
      (by fin_cases v <;> decide +kernel) (by fin_cases v <;> decide +kernel)
      (by decide +kernel) _ _ wallMarker))
  have first := near.1
  norm_num [inside_pullX] at first
  exact apart _ p hf 2304 512 (by fin_cases v <;> decide +kernel)
    (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
    ⟨first,southeast_near v p hf⟩

theorem northeast_top (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) :
    (owner p 1024).Inside (12/5) 3 ∧ (owner p 1024).Inside (113/50) 3 := by
  obtain ⟨_,_,_,_,_,_,_,_,ne⟩ := compulsory v p hf
  have no5 : 5∉auxiliaries p 1024 := by
    intro owned
    have first := aux_inside p 1024 5 (by norm_num) owned
    norm_num [auxPoints,fPoints,gPoints] at first
    exact apart _ p hf 1024 2304 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _
      ⟨first,merged_inward v p hf⟩
  have seven : 7∈auxiliaries p 1024 := ne.resolve_left no5
  constructor
  · simpa [auxPoints,fPoints,gPoints] using aux_inside p 1024 7 (by norm_num) seven
  · simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 8

/-- Every canonical sign of the actual merged owner reaches the center.
The neighboring SE, singleton, wall and top owners supply each exclusion. -/
theorem merged_center (v : Fin 2) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family v) : (owner p 2304).Inside 2 2 := by
  obtain ⟨sw,_,_,_,left,south,_,top,_⟩ := compulsory v p hf
  have markSW : (owner p 2304).Inside (33/20) (33/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markNW : (owner p 2304).Inside (33/20) (47/20) := by
    have h := seed_point v p hf 2304 (by fin_cases v <;> decide +kernel)
      (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have low : (owner p 2).Inside 1 (87/50) := by
    have h := seed_point v p hf 2 (by fin_cases v <;> decide +kernel)
      (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  have high : (owner p 4096).Inside 1 (113/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 4096 1 (by norm_num) left
  have inward : (owner p 512).Inside 2 (87/50) := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 512 4 (by norm_num) south
  have bottom : (owner p 1).Inside (8/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 1 2 (by norm_num) sw
  have topPoint : (owner p 32768).Inside (8/5) 3 := by
    simpa [auxPoints,fPoints,gPoints] using aux_inside p 32768 3 (by norm_num) top
  have wallMarker : (owner p 4096).Inside (457/500) 2 := by
    have h := seed_point v p hf 4096 (by fin_cases v <;> decide +kernel)
      (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  have wallHigh : (owner p 4096).Inside 1 (12/5) := by
    simpa [claims,auxPoints,gPoints] using C580581Entrance.inside v p hf 5
  exact MergedLeftCenter.point (owner p 2304) (owner p 4096) (side p 2304)
    ((p.congruent _).trans (p.congruent _).symm) (box p 4096) markSW markNW
    (foreign v p hf 2304 2 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ low)
    (foreign v p hf 2304 4096 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ high)
    (foreign v p hf 2304 512 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ inward)
    (foreign v p hf 2304 1 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ bottom)
    (foreign v p hf 2304 32768 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel) _ _ topPoint)
    wallMarker wallHigh
    (apart _ p hf 2304 4096 (by fin_cases v <;> decide +kernel)
      (by fin_cases v <;> decide +kernel) (by decide +kernel))

#print axioms southeast_near
#print axioms merged_inward
#print axioms northeast_top
#print axioms merged_center
end
end N12Compact.FiniteCases.C580581CentralEntrance

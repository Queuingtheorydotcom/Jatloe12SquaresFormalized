import Compact.Completion.FiniteCases.C896CentralPoints
import Compact.Completion.OtherCases.TwoChordHull
import Compact.Completion.OtherCases.ShortCornerAdvance
import Compact.Completion.OtherCases.ShorterCornerWall

/-! A genuine inward point of the one merged lower C896 square.
Mask768 is G-exempt, so no positive G lower budget is assumed. Omission
of G6 instead forces three strict hull points against actual bottom8192
and the actual paired southeast corner12. No northeast-corner marker,
upper right bar, or disjoint split of merged768 occurs. Source only. -/
namespace N12Compact.FiniteCases.C896Ending
open S12 S12Pilot C896Domains
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
noncomputable section
set_option Elab.async false

theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed family p hf mask member P checked

theorem aux_point (p : NormalizedPacking) (mask index : Nat) (bound : index<20)
    (owned : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr owned

theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (x y : ℝ) (owned : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun own => apart family p hf m n hm hn different x y ⟨own,owned⟩

theorem bottom_marker (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 8192).Inside 2 (457/500) := by
  convert seed_point p hf 8192 (by decide +kernel) (2,457/500) (by decide +kernel)
    using 1 <;> norm_num

theorem bottom_g5 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 8192).Inside (113/50) 1 := by
  simpa [auxPoints,fPoints,gPoints] using aux_point p 8192 15 (by norm_num)
    (C896Entrance.compulsory p hf).bottom.2

/-- The true southeast corner advances downwards using actual right
G8 and the strict high point of the actual bottom8192. -/
theorem southeast_corner_advance (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : (owner p 12).Inside 3 (39/50) := by
  have origin : (owner p 12).Inside 3 1 := by
    convert seed_point p hf 12 (by decide +kernel) (3,1) (by decide +kernel)
      using 1 <;> norm_num
  have right : (owner p 16384).Inside 3 (8/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 16384 18 (by norm_num)
      (C896Entrance.compulsory p hf).rightWall.2
  let K := (pullX (pullSwap (owner p 12))).translated 3 3
  have wall : ∀ x y,K.Inside x y → y≤1 := by
    intro x y own
    have back := own
    simp only [K,inside_translated_iff,inside_pullX,inside_pullSwap] at back
    have bound := box p 12 _ _ back
    linarith only [bound.2.1]
  have point := ShortCornerAdvance.point K (side p 12) wall
    (by norm_num [K,inside_translated_iff,inside_pullX,inside_pullSwap]; exact origin)
    (by norm_num [K,inside_translated_iff,inside_pullX,inside_pullSwap]
        exact foreign p hf 12 16384 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ right)
    (by norm_num [K,inside_translated_iff,inside_pullX,inside_pullSwap]
        exact foreign p hf 12 8192 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ (C896WallBars.bottom_right p hf))
  norm_num [K,inside_translated_iff,inside_pullX,inside_pullSwap] at point
  exact point

/-- The reflected-transposed chart is precisely
(x_local,y_local)=(2-y_original,x_original-2). Its whole excluded
slant is the segment from the actual bottom marker to its actual G5. -/
theorem merged_lower_hull (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 768).Inside (113/50) 2) :
    (owner p 768).Inside 2 (49/50) ∧ (owner p 768).Inside (101/50) (49/50) ∧
      (owner p 768).Inside (211/100) (26/25) := by
  have h := C896CentralPoints.fixed p hf
  have singleton : (owner p 1).Inside (87/50) 1 := by
    convert seed_point p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
      using 1 <;> norm_num
  let A := (pullX (pullSwap (owner p 768))).translated 2 2
  have hull := TwoChordHull.points A (side p 768)
    (by norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap]; exact h.southwestMarker)
    (by norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap]; exact h.southeastMarker)
    (by norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap]
        exact foreign p hf 768 2048 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ h.northwestG3)
    (by norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap]; exact missing)
    (by norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap]
        exact foreign p hf 768 1 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ singleton)
    (by norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap]
        exact foreign p hf 768 8192 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ (bottom_g5 p hf))
    (by
      intro z low high own
      have back := own
      simp only [A,inside_translated_iff,inside_pullX,inside_pullSwap] at back
      have segment := inside_segment (owner p 8192) 2 (457/500) (113/50) 1 z
        (bottom_marker p hf) (bottom_g5 p hf) low high
      have duplicate : (owner p 768).Inside
          ((1-z)*2+z*(113/50)) ((1-z)*(457/500)+z*1) := by
        convert back using 1 <;> ring
      exact apart family p hf 768 8192 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨duplicate,segment⟩)
  norm_num [A,inside_translated_iff,inside_pullX,inside_pullSwap] at hull
  exact hull

/-- The full actual bottom wall rules out the three hull points. This
is the geometric producer of merged G6, with no G-count shortcut. -/
theorem merged_g6_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 768).Inside (113/50) 2 := by
  by_contra missing
  have hull := merged_lower_hull p hf missing
  let B := (pullX (pullSwap (owner p 8192))).translated 3 2
  apply ShorterCornerWall.impossible B (side p 8192)
  · intro x y own
    have back := own
    simp only [B,inside_translated_iff,inside_pullX,inside_pullSwap] at back
    have bound := box p 8192 _ _ back
    linarith only [bound.2.2.1]
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact bottom_marker p hf
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact bottom_g5 p hf
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact C896WallBars.bottom_right p hf
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact foreign p hf 8192 768 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ hull.1
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact foreign p hf 8192 768 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ hull.2.1
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact foreign p hf 8192 768 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ hull.2.2
  · norm_num [B,inside_translated_iff,inside_pullX,inside_pullSwap]
    exact foreign p hf 8192 12 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (southeast_corner_advance p hf)

theorem merged_g6 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    16∈auxiliaries p 768 := by
  apply (auxiliary_exact p 768 16 (by norm_num)).mp
  simpa [auxPoints,fPoints,gPoints] using merged_g6_point p hf

end
#print axioms southeast_corner_advance
#print axioms merged_g6_point
end N12Compact.FiniteCases.C896Ending

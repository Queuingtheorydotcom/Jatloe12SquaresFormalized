import Compact.Completion.FiniteCases.C975IncomingCut
import Compact.Completion.OtherCases.C1089.ContinuousBottom
import Compact.Completion.OtherCases.ElbowPoint

/-! C1090's initial crosspoint and southeast selection reductions,
applied to the authentic C975 family. The horizontal and vertical bars
belong to the two distinct singletons 1 and 2. The northwest marker is
strict in merged top34816 throughout. Every point below is produced
from the existing original-family entrance. Source only, uncompiled. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed _ p hf mask member P checked

theorem aux_point (p : NormalizedPacking) (mask index : Nat)
    (bound : index<20) (own : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr own

theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (x y : ℝ) (own : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun h => apart _ p hf m n hm hn different x y ⟨h,own⟩

structure Fixed (p : NormalizedPacking) : Prop where
  southwestMarker : (owner p 256).Inside (33/20) (33/20)
  southwestF4 : (owner p 256).Inside 2 (87/50)
  southwestG3 : (owner p 256).Inside (87/50) 2
  southeastMarker : (owner p 512).Inside (47/20) (33/20)
  southeastF8 : (owner p 512).Inside 3 (87/50)
  northeastMarker : (owner p 1024).Inside (47/20) (47/20)
  northwestMarker : (owner p 34816).Inside (33/20) (47/20)
  topMarker : (owner p 34816).Inside 2 (1543/500)
  bottomMarker : (owner p 8192).Inside 2 (457/500)
  bottomF6 : (owner p 8192).Inside (12/5) 1
  bottomG5 : (owner p 8192).Inside (113/50) 1
  rightMarker : (owner p 16384).Inside (1543/500) 2
  rightF9 : (owner p 16384).Inside 3 (113/50)
  rightG9 : (owner p 16384).Inside 3 (12/5)
  southeastCorner : (owner p 12).Inside 3 1
  southeastCornerRight : (owner p 12).Inside (1543/500) 1

theorem fixed (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Fixed p := by
  have h := compulsory p hf
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · convert seed_point p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel) using 1 <;> norm_num
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 256 4 (by norm_num) h.southwestCentral.1
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 256 13 (by norm_num) h.southwestCentral.2
  · convert seed_point p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel) using 1 <;> norm_num
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 512 8 (by norm_num) h.southeast.1
  · convert seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel) using 1 <;> norm_num
  · convert seed_point p hf 34816 (by decide +kernel) (33/20,47/20) (by decide +kernel) using 1 <;> norm_num
  · convert seed_point p hf 34816 (by decide +kernel) (2,1543/500) (by decide +kernel) using 1 <;> norm_num
  · convert seed_point p hf 8192 (by decide +kernel) (2,457/500) (by decide +kernel) using 1 <;> norm_num
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 8192 6 (by norm_num) h.bottom.1
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 8192 15 (by norm_num) h.bottom.2
  · convert seed_point p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel) using 1 <;> norm_num
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 16384 9 (by norm_num) h.rightWall.1
  · simpa [auxPoints,fPoints,gPoints] using aux_point p 16384 19 (by norm_num) h.rightWall.2
  · convert seed_point p hf 12 (by decide +kernel) (3,1) (by decide +kernel) using 1 <;> norm_num
  · convert seed_point p hf 12 (by decide +kernel) (1543/500,1) (by decide +kernel) using 1 <;> norm_num

theorem singleton_horizontal (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (x : ℝ) (low : 28/25≤x) (high : x≤87/50) : (owner p 1).Inside x 1 := by
  apply horizontal_segment (owner p 1) (28/25) (87/50) 1 x
  · convert seed_point p hf 1 (by decide +kernel) (28/25,1) (by decide +kernel) using 1 <;> norm_num
  · convert seed_point p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · exact low
  · exact high

theorem singleton_vertical (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 28/25≤y) (high : y≤87/50) : (owner p 2).Inside 1 y := by
  apply vertical_segment (owner p 2) 1 (28/25) (87/50) y
  · convert seed_point p hf 2 (by decide +kernel) (1,28/25) (by decide +kernel) using 1 <;> norm_num
  · convert seed_point p hf 2 (by decide +kernel) (1,87/50) (by decide +kernel) using 1 <;> norm_num
  · norm_num
  · exact low
  · exact high

theorem southwest_south (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 256).Inside 2 (3/2) := by
  have h := fixed p hf
  have result := C981CompletionCrosspoint.point (pullY (pullX (owner p 256))) (side p 256)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestF4)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestG3)
    (by norm_num [inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 256 34816 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 256 512 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southeastMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (singleton_vertical p hf _ (by norm_num) (by norm_num)))
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (singleton_vertical p hf _ (by norm_num) (by norm_num)))
  norm_num [inside_pullY,inside_pullX] at result
  exact result

theorem southwest_west (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 256).Inside (3/2) 2 := by
  have h := fixed p hf
  have result := C981CompletionCrosspoint.point
    (pullSwap (pullY (pullX (owner p 256)))) (side p 256)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestG3)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestF4)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 256 512 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southeastMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 256 34816 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northwestMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (singleton_horizontal p hf _ (by norm_num) (by norm_num)))
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact foreign p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (singleton_horizontal p hf _ (by norm_num) (by norm_num)))
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at result
  exact result

theorem southeast_g8_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 512).Inside 3 (8/5) := by
  have h := fixed p hf
  by_contra missing
  have elbow : (owner p 512).Inside (113/50) 2 := by
    rcases (compulsory p hf).southeast.2 with own | own
    · simpa [auxPoints,fPoints,gPoints] using aux_point p 512 16 (by norm_num) own
    · apply False.elim
      apply missing
      simpa [auxPoints,fPoints,gPoints] using aux_point p 512 18 (by norm_num) own
  have duplicate := (N12Compact.Completion.OtherCases.ElbowPoint.points_original (owner p 512)
    (side p 512) h.southeastMarker elbow h.southeastF8
    (foreign p hf 512 1024 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.northeastMarker) missing
    (foreign p hf 512 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.rightMarker)).1
  exact apart _ p hf 256 512 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨southwest_south p hf,duplicate⟩

theorem southeast_g8 (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    18∈auxiliaries p 512 := by
  apply (auxiliary_exact p 512 18 (by norm_num)).mp
  simpa [auxPoints,fPoints,gPoints] using southeast_g8_point p hf

/-- The full horizontal interval stays in the single actual bottom8192.
Its off-row foreign seed stays in singleton1. No center sign is assumed. -/
theorem bottom_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 8192).Inside (14/5) 1 ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → (owner p 8192).Inside x 1 := by
  have h := fixed p hf
  have off : (owner p 1).Inside (187/100) (19/25) := by
    convert seed_point p hf 1 (by decide +kernel) (187/100,19/25) (by decide +kernel) using 1 <;> norm_num
  exact (N12Compact.Completion.OtherCases.C1089.ContinuousBottom.reach (owner p 8192)
    (side p 8192) (box p 8192) h.bottomMarker h.bottomF6 h.bottomG5
    (foreign p hf 8192 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ (singleton_horizontal p hf _ (by norm_num) (by norm_num)))
    (foreign p hf 8192 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ off)
    (foreign p hf 8192 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.southeastMarker)).2

#print axioms southwest_south
#print axioms southwest_west
#print axioms southeast_g8
#print axioms bottom_reach
end
end N12Compact.FiniteCases.C975Selection

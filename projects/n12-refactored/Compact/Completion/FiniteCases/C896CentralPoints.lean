import Compact.Completion.FiniteCases.C896WallBars
import Compact.Completion.CommonCases.C974976Origins
import Compact.Completion.C981.Crosspoint
import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.WallSignFromSingleton

/-! Further actual C896 geometry. Both northwest crosspoints use the
genuine left/top bars, and the top origin uses the actual northwest
paired corner. The merged lower owner remains one physical square and
retains every optional G membership. -/
namespace N12Compact.FiniteCases.C896CentralPoints
open S12 S12Pilot C896Domains
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

private theorem point (p : NormalizedPacking) (mask index : Nat) (bound : index<20)
    (owned : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr owned

structure Fixed (p : NormalizedPacking) : Prop where
  northwestMarker : (owner p 2048).Inside (33/20) (47/20)
  northeastMarker : (owner p 1024).Inside (47/20) (47/20)
  southwestMarker : (owner p 768).Inside (33/20) (33/20)
  southeastMarker : (owner p 768).Inside (47/20) (33/20)
  northwestF5 : (owner p 2048).Inside 2 (113/50)
  northwestG3 : (owner p 2048).Inside (87/50) 2
  topMarker : (owner p 32768).Inside 2 (1543/500)
  topF3 : (owner p 32768).Inside (8/5) 3
  leftMarker : (owner p 4096).Inside (457/500) 2
  leftG1 : (owner p 4096).Inside 1 (12/5)
  northwestCornerMarker : (owner p 192).Inside 1 (1543/500)
  northwestCorner : (owner p 192).Inside 1 3

theorem fixed (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Fixed p where
  northwestMarker := by
    convert seed _ p hf 2048 (by decide +kernel) (33/20,47/20) (by decide +kernel) using 1 <;> norm_num
  northeastMarker := by
    convert seed _ p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel) using 1 <;> norm_num
  southwestMarker := by
    convert seed _ p hf 768 (by decide +kernel) (33/20,33/20) (by decide +kernel) using 1 <;> norm_num
  southeastMarker := by
    convert seed _ p hf 768 (by decide +kernel) (47/20,33/20) (by decide +kernel) using 1 <;> norm_num
  northwestF5 := by
    simpa [auxPoints,fPoints,gPoints] using
      point p 2048 5 (by norm_num) (C896Entrance.compulsory p hf).northwest.1
  northwestG3 := by
    simpa [auxPoints,fPoints,gPoints] using
      point p 2048 13 (by norm_num) (C896Entrance.compulsory p hf).northwest.2
  topMarker := by
    convert seed _ p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel) using 1 <;> norm_num
  topF3 := by
    simpa [auxPoints,fPoints,gPoints] using
      point p 32768 3 (by norm_num) (C896Entrance.compulsory p hf).top.1
  leftMarker := by
    convert seed _ p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel) using 1 <;> norm_num
  leftG1 := by
    simpa [auxPoints,fPoints,gPoints] using
      point p 4096 11 (by norm_num) (C896Entrance.compulsory p hf).leftWall.2
  northwestCornerMarker := by
    convert seed _ p hf 192 (by decide +kernel) (1,1543/500) (by decide +kernel) using 1 <;> norm_num
  northwestCorner := by
    convert seed _ p hf 192 (by decide +kernel) (1,3) (by decide +kernel) using 1 <;> norm_num

private theorem foreign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (x y : ℝ) (owned : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
  fun own => apart _ p hf m n hm hn different x y ⟨own,owned⟩

theorem northwest_north (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2048).Inside 2 (5/2) := by
  have h := fixed p hf
  have bars := C896WallBars.bars p hf
  have result := C981CompletionCrosspoint.point (pullX (owner p 2048)) (side p 2048)
    (by norm_num [inside_pullX]; exact h.northwestF5)
    (by norm_num [inside_pullX]; exact h.northwestG3)
    (by norm_num [inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullX]; exact foreign p hf 2048 768
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southwestMarker)
    (by norm_num [inside_pullX]; exact foreign p hf 2048 1024
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northeastMarker)
    (by norm_num [inside_pullX]; exact foreign p hf 2048 4096
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (bars.left _ (by norm_num) (by norm_num)))
    (by norm_num [inside_pullX]; exact foreign p hf 2048 4096
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (bars.left _ (by norm_num) (by norm_num)))
  norm_num [inside_pullX] at result
  exact result

theorem northwest_west (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2048).Inside (3/2) 2 := by
  have h := fixed p hf
  have bars := C896WallBars.bars p hf
  have result := C981CompletionCrosspoint.point (pullSwap (pullX (owner p 2048))) (side p 2048)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestG3)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestF5)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact foreign p hf 2048 1024
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northeastMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact foreign p hf 2048 768
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southwestMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact foreign p hf 2048 32768
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (bars.top _ (by norm_num) (by norm_num)))
    (by norm_num [inside_pullSwap,inside_pullX]; exact foreign p hf 2048 32768
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (bars.top _ (by norm_num) (by norm_num)))
  norm_num [inside_pullSwap,inside_pullX] at result
  exact result

theorem northwest_sharp (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2048).Inside (73/50) (201/100) := by
  have h := fixed p hf
  have result := CommonCases.InwardPoint.strong_original (pullY (pullX (owner p 2048)))
    (side p 2048)
    (by norm_num [inside_pullY,inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact h.northwestF5)
    (by norm_num [inside_pullY,inside_pullX]; exact h.northwestG3)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 2048 1024
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northeastMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 2048 768
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southwestMarker)
    (by norm_num [inside_pullY,inside_pullX]; exact foreign p hf 2048 32768
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.topF3)
  norm_num [inside_pullY,inside_pullX] at result
  exact result

theorem top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 32768).Inside 2 3 := by
  have h := fixed p hf
  have singleton : (owner p 2).Inside 1 (87/50) := by
    convert seed _ p hf 2 (by decide +kernel) (1,87/50) (by decide +kernel) using 1 <;> norm_num
  exact CommonCases.C974976Central.top_origin _ _ _ (side p 4096) (side p 32768)
    ((p.congruent _).trans (p.congruent _).symm)
    (box p 4096) (box p 32768) (box p 192) h.leftMarker h.leftG1
    (foreign p hf 4096 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ singleton)
    (foreign p hf 4096 2048 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northwestG3)
    h.topMarker h.topF3 h.northwestCornerMarker h.northwestCorner
    (apart _ p hf 192 4096 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (apart _ p hf 192 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem left_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    2<centerY (owner p 4096) :=
  CommonCases.WallSignFromSingleton.original_left_center family p hf 4096
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem bottom_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    2<centerX (owner p 8192) :=
  (CommonCases.WallSignFromSingleton.original_bottom family p hf 8192
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).1

end
#print axioms northwest_north
#print axioms northwest_west
#print axioms northwest_sharp
#print axioms top_origin
end N12Compact.FiniteCases.C896CentralPoints

import Compact.Completion.FiniteCases.C896MergedInward
import Compact.Geometry.MergedLeftNegative
import Compact.Geometry.CentralWallCenter

/-! Two genuine actual C896 owners contain the container center.
The merged bottom remains one square through its full transposed
center proof. The NW center uses the actual left and top wall squares;
their omitted points are in the true singleton2 and singleton16.
No NE corner pair, global marker32 owner or upper right bar is used.
This is uncompiled source. -/
namespace N12Compact.FiniteCases.C896Ending
open S12 S12Pilot C896Domains
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

theorem merged_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 768).Inside 2 2 := by
  have h := C896CentralPoints.fixed p hf
  have low : (owner p 1).Inside (87/50) 1 := by
    convert seed_point p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
      using 1 <;> norm_num
  have top : (owner p 16384).Inside 3 (8/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 16384 18 (by norm_num)
      (C896Entrance.compulsory p hf).rightWall.2
  have bottomF6 : (owner p 8192).Inside (12/5) 1 := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 8192 6 (by norm_num)
      (C896Entrance.compulsory p hf).bottom.1
  obtain ⟨A,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame (pullSwap (owner p 768))
  have south : A.Inside (33/20) (33/20) :=
    (inside _ _).mpr ((inside_pullSwap _ _ _).mpr h.southwestMarker)
  have north : A.Inside (33/20) (47/20) :=
    (inside _ _).mpr ((inside_pullSwap _ _ _).mpr h.southeastMarker)
  have inner : A.Inside 2 (113/50) :=
    (inside _ _).mpr ((inside_pullSwap _ _ _).mpr (merged_g6_point p hf))
  have bounds := abs_le.mp range
  have result : A.Inside 2 2 := by
    by_cases sign : 0≤A.s
    · refine ⟨?_,?_,?_,?_⟩
      · linarith only [south.1,cp,sign]
      · linarith only [inner.2.1,sign]
      · linarith only [south.2.2.1,bounds.2]
      · linarith only [north.2.2.2,cp,sign]
    · apply MergedLeftNegative.point A (pullSwap (owner p 8192))
        (by simpa only [shape,pullSwap] using side p 768)
        (shape.trans ((p.congruent _).trans (p.congruent _).symm))
        (container_pullSwap _ (box p 8192)) cp (le_of_not_ge sign)
        (by linarith only [bounds.1]) south north
      · intro own
        exact foreign p hf 768 1 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ low ((inside_pullSwap _ _ _).mp ((inside _ _).mp own))
      · intro own
        exact foreign p hf 768 8192 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ (bottom_g5 p hf)
          ((inside_pullSwap _ _ _).mp ((inside _ _).mp own))
      · intro own
        exact foreign p hf 768 16384 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ top ((inside_pullSwap _ _ _).mp ((inside _ _).mp own))
      · exact (inside_pullSwap _ _ _).mpr (bottom_marker p hf)
      · exact (inside_pullSwap _ _ _).mpr bottomF6
      · intro x y both
        exact apart family p hf 768 8192 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) y x
          ⟨(inside_pullSwap _ _ _).mp ((inside x y).mp both.1),
            (inside_pullSwap _ _ _).mp both.2⟩
  exact (inside_pullSwap _ _ _).mp ((inside _ _).mp result)

/-- Reflecting the actual NW and both actual neighboring wall owners
gives the complete two-wall center theorem. The singleton upper-right
mask16 supplies only its genuine G7; no paired NE corner is needed. -/
theorem northwest_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2048).Inside 2 2 := by
  have h := C896CentralPoints.fixed p hf
  have singleton : (owner p 2).Inside 1 (87/50) := by
    convert seed_point p hf 2 (by decide +kernel) (1,87/50) (by decide +kernel)
      using 1 <;> norm_num
  have northeastSingleton : (owner p 16).Inside (113/50) 3 := by
    convert seed_point p hf 16 (by decide +kernel) (113/50,3) (by decide +kernel)
      using 1 <;> norm_num
  have point := CentralWallCenter.point (pullX (owner p 2048)) (pullX (owner p 4096))
    (pullX (owner p 32768)) (side p 2048)
    ((p.congruent _).trans (p.congruent _).symm)
    ((p.congruent _).trans (p.congruent _).symm)
    (container_pullX _ (box p 4096)) (container_pullX _ (box p 32768))
    (by norm_num [inside_pullX]; exact h.northwestF5)
    (by norm_num [inside_pullX]; exact h.northwestG3)
    (by norm_num [inside_pullX]; exact h.northwestMarker)
    (by norm_num [inside_pullX]; exact foreign p hf 2048 768 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southwestMarker)
    (by norm_num [inside_pullX]; exact foreign p hf 2048 1024 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.northeastMarker)
    (by norm_num [inside_pullX]; exact h.leftMarker)
    (by norm_num [inside_pullX]; exact h.leftG1)
    (by norm_num [inside_pullX]; exact foreign p hf 4096 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ singleton)
    (by norm_num [inside_pullX]; exact h.topMarker)
    (by norm_num [inside_pullX]; exact h.topF3)
    (by norm_num [inside_pullX]; exact foreign p hf 32768 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ northeastSingleton)
    (by
      intro x y both
      exact apart family p hf 2048 4096 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _
        ⟨(inside_pullX _ _ _).mp both.1,(inside_pullX _ _ _).mp both.2⟩)
    (by
      intro x y both
      exact apart family p hf 2048 32768 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _
        ⟨(inside_pullX _ _ _).mp both.1,(inside_pullX _ _ _).mp both.2⟩)
  norm_num [inside_pullX] at point
  exact point

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False :=
  apart family p hf 768 2048 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 2 2 ⟨merged_center p hf,northwest_center p hf⟩

end
#print axioms merged_center
#print axioms northwest_center
#print axioms impossible
end N12Compact.FiniteCases.C896Ending

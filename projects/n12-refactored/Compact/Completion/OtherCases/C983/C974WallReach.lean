import Compact.Completion.OtherCases.C983.C974CornerScalars
import Compact.Completion.OtherCases.WallProfile.CornerProfile

/-! Section 3 of C974-THREE-SQUARE-ENDING. W is in that chapter's
translated chart, with its origin (0,0) and actual corner at (1,0).
The lower-face premise is precisely the conclusion of its Section 2. -/
namespace N12Compact.Completion.OtherCases.C983.C974WallReach
open S12 S12Pilot
set_option Elab.async false

structure Data (W : OpenSquare) : Prop where
  sideLarge : 1<W.side
  cosine : 0<W.c
  sine : 0<W.s
  canonical : W.s≤W.c
  slope : 3*W.s<2*W.c
  origin : W.Inside 0 0
  far : W.Inside (4/5) 0
  upperU : W.loU+W.side≤W.c
  upperV : W.loV+W.side≤W.c/2
  lowerFace : -(W.s/(1+W.c))*(1-W.s)<W.loU

theorem frame_bounds (W : OpenSquare) (h : Data W) :
    4/5<W.c ∧ W.c≤1 ∧ 0<W.s/(1+W.c) ∧ W.s/(1+W.c)<1/3 := by
  have cu : W.c≤1 := by nlinarith only [W.unit_normal,sq_nonneg W.s,h.cosine]
  have square := mul_pos (sub_pos.mpr h.slope)
    (show 0<2*W.c+3*W.s by linarith only [h.cosine,h.sine])
  have cp : 4/5<W.c := by nlinarith only [square,W.unit_normal,h.cosine]
  have denominator : 0<1+W.c := by linarith only [h.cosine]
  have hp : 0<W.s/(1+W.c) := div_pos h.sine denominator
  have hu : W.s/(1+W.c)<1/3 := (div_lt_iff₀ denominator).mpr
    (by linarith only [h.slope,cu])
  exact ⟨cp,cu,hp,hu⟩

/-- The strict point R** and the stronger upper-u support, equations
(18)--(23), in the same actual wall square. -/
theorem reach (W : OpenSquare) (h : Data W) :
    ∃ beta : ℝ,0<beta ∧ W.Inside 1 (-beta) ∧
      W.s/(1+W.c)-1/2< -beta ∧ W.s<1/2 ∧
      W.side-W.s/2<W.loU+W.side := by
  let z := W.s/(1+W.c)
  let k := z*(1-W.s)
  let beta := (1+z^2)/2-2*z
  have frame := frame_bounds W h
  have zp : 0<z := frame.2.2.1
  have zu : z<1/3 := frame.2.2.2
  have denominator : 1+W.c≠0 := by linarith only [h.cosine]
  have zn : 1+z^2≠0 := by positivity
  have forms := C974CornerScalars.normal_forms W.c W.s h.cosine.le h.sine.le W.unit_normal
  have dform : W.c=(1-z^2)/(1+z^2) := forms.2.2.1
  have tform : W.s=2*z/(1+z^2) := forms.2.2.2
  have oneMinus : W.s*z=1-W.c := by
    dsimp only [z]
    field_simp [denominator]
    nlinarith only [W.unit_normal]
  have gap : 1-W.c<k := by
    dsimp only [k]
    linarith only [h.lowerFace,h.upperU,h.sideLarge]
  have small : W.s<1/2 := by
    apply lt_of_not_ge
    intro bad
    have impossible := mul_nonneg zp.le (show 0≤2*W.s-1 by linarith only [bad])
    dsimp only [k] at gap
    nlinarith only [impossible,oneMinus,gap]
  have betaPositive : 0<beta := by
    have product := mul_pos (show 0<1+z^2 by positivity)
      (show 0<1-2*W.s by linarith only [small])
    have identity : 2*beta=(1+z^2)*(1-2*W.s) := by
      rw [tform]
      dsimp only [beta]
      field_simp [zn]
      ring
    linarith only [identity,product]
  have uProjection : W.c-W.s*beta=1-k := by
    dsimp only [k,beta]
    rw [dform,tform]
    field_simp [zn]
    ring
  have height : z-1/2< -beta := by
    have product := mul_pos zp (show 0<1-z/2 by linarith only [zu])
    dsimp only [beta]
    nlinarith only [product]
  have transverse : W.s+W.c*(1/2+beta)<1 := by
    have product : 0<z^2*(3-z)*(1-z) := by
      have first : 0<3-z := by linarith only [zu]
      have last : 0<1-z := by linarith only [zu]
      positivity
    have identity :
        2*(1+z^2)*(1-(W.s+W.c*(1/2+beta)))=z^2*(3-z)*(1-z) := by
      dsimp only [beta]
      rw [dform,tform]
      field_simp [zn]
      ring
    apply lt_of_not_ge
    intro bad
    have impossible := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤2*(1+z^2) by positivity)
      (show 1-(W.s+W.c*(1/2+beta))≤0 by linarith only [bad])
    linarith only [identity,product,impossible]
  have kp : k<1 := by
    have product := mul_pos zp h.sine
    dsimp only [k]
    nlinarith only [zu,product]
  have o := h.origin
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero] at o
  have point : W.Inside 1 (-beta) := by
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [o.1,uProjection,kp]
    · dsimp only [k] at uProjection
      nlinarith only [h.lowerFace,h.sideLarge,uProjection]
    · nlinarith only [h.upperV,h.sideLarge,transverse]
    · have positive := mul_pos betaPositive h.cosine
      nlinarith only [o.2.2.2,h.sine,positive]
  have strong : k<W.s/2 := by
    have positive : 0<z^2*(2-z) := by
      have last : 0<2-z := by linarith only [zu]
      positivity
    have identity : (1+z^2)*(W.s/2-k)=z^2*(2-z) := by
      dsimp only [k]
      rw [tform]
      field_simp [zn]
      ring
    apply lt_of_not_ge
    intro bad
    have impossible := mul_nonpos_of_nonneg_of_nonpos (show 0≤1+z^2 by positivity)
      (show W.s/2-k≤0 by linarith only [bad])
    linarith only [identity,positive,impossible]
  refine ⟨beta,betaPositive,point,height,small,?_⟩
  dsimp only [k] at strong
  linarith only [strong,h.lowerFace]

end N12Compact.Completion.OtherCases.C983.C974WallReach

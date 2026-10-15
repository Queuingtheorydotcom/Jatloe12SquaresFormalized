import Compact.Completion.C1092.MPPMNegativeForwardScalars
import Compact.Completion.C1092.WholeSupports
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Geometry.ClosedPointExclusion

/-! NEGATIVE-FORWARD-POSITIVE-H sections 2--4. Every face is derived
from its literal point. The whole bottom bar remains in one actual open
square B, including in the tangent-vertex case. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeForward
open S12 S12Pilot FourSquareAnchors C977CornerCubic
open Completion.OtherCases
set_option Elab.async false

structure Input (C E B : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  sourceNormal : Normal C.c (-C.s)
  targetNormal : Normal E.c E.s
  source : C.Inside (-7/20) (-7/20)
  ordinary : C.Inside (-1) (-13/50)
  outer : C.Inside (-1) (-2/5)
  forward : C.Inside (-13/50) 0
  previous : ¬C.Inside (-1) 0
  northwest : ¬C.Inside (-7/20) (7/20)
  target : E.Inside (7/20) (-7/20)
  bar0 : E.Inside (13/50) (-1)
  bar1 : E.Inside (2/5) (-1)
  inner : E.Inside 0 (-13/50)
  wholeBar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)
  apartBar : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)

structure SourceProfile (C : OpenSquare) : Prop where
  negative : 0< -C.s
  close : 87/100<C.c
  small : -C.s<49/100
  strictCosine : C.c<1
  lowerU : -C.c≤C.loU
  upperU : C.loU+C.side≤-(13/50)*C.s
  upperV : C.loV+C.side≤(7/20)*(C.c+C.s)
  lowerV : -C.c+(14/25)*C.s≤C.loV

theorem source_profile (C E B : OpenSquare) (h : Input C E B) : SourceProfile C := by
  have cb := normal_bounds h.sourceNormal
  have cp : 0<C.c := by linarith only [cb.1]
  have sn := h.sourceNormal.1
  have order := h.sourceNormal.2.1
  have lowerU : -C.c≤C.loU := by
    apply le_of_not_gt
    intro low
    apply h.previous
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.ordinary.2.1,h.outer.2.2.1,h.forward.2.2.2,cp,sn,order]
  have upperU : C.loU+C.side≤-(13/50)*C.s := by
    apply le_of_not_gt
    intro high
    apply h.apart 0 (-13/50)
    refine ⟨?_,h.inner⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.ordinary.1,h.ordinary.2.2.1,h.forward.2.2.2,cp,sn,order]
  have upperV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt
    intro high
    apply h.northwest
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.ordinary.1,h.forward.2.1,h.forward.2.2.1,cp,sn,order]
  have angle := source_angle h.sourceNormal
    (show 1<C.c+(13/50)*(-C.s) by linarith only [lowerU,upperU,h.side])
  have lowerV : -C.c+(14/25)*C.s≤C.loV := by
    apply le_of_not_gt
    intro low
    apply h.apartBar (-14/25) (-1)
    refine ⟨?_,h.wholeBar _ (by norm_num) (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.ordinary.1,h.ordinary.2.2.2,lowerU,h.side,
        cp,sn,order,cb.2.1,angle.2.2.1]
  exact ⟨angle.1,angle.2.1,angle.2.2.1,angle.2.2.2,lowerU,upperU,upperV,lowerV⟩

private theorem above_bar (C B : OpenSquare) (X Y : ℝ)
    (closed : ClosedInside C X Y) (forward : C.Inside (-13/50) 0)
    (xl : -14/25≤X) (xu : X≤0)
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : -1<Y := by
  apply lt_of_not_ge
  intro below
  let t := (-1-Y)/(-Y)
  have den : 0< -Y := by linarith only [below]
  have tn : 0≤t := div_nonneg (by linarith only [below]) den.le
  have tu : t≤1 := (div_le_one den).mpr (by norm_num)
  have relation : t*(-Y)= -1-Y := div_mul_cancel₀ _ den.ne'
  have coordinate : (1-t)*Y+t*0= -1 := by nlinarith only [relation]
  have low : -14/25≤(1-t)*X+t*(-13/50) := by
    have product := mul_nonneg (show 0≤1-t by linarith only [tu])
      (show 0≤X+14/25 by linarith only [xl])
    nlinarith only [product,tn]
  have high : (1-t)*X+t*(-13/50)≤0 := by
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-t by linarith only [tu]) xu
    nlinarith only [product,tn]
  have point := ClosedPointExclusion.closed_segment C X Y (-13/50) 0 t
    closed ⟨forward.1.le,forward.2.1.le,forward.2.2.1.le,forward.2.2.2.le⟩ tn tu
  rw [coordinate] at point
  exact ClosedPointExclusion.outside_of_closed B C _ _
    (fun x y own => apart x y ⟨own.2,own.1⟩) point (bar _ low high)

/-- The actual lowest vertex lies strictly above the real foreign bar;
its abscissa is controlled before any wall conclusion is made. -/
theorem center_floor (C E B : OpenSquare) (h : Input C E B) (f : SourceProfile C) :
    -1+C.side*(C.c-C.s)/2<centerY C := by
  have cp : 0<C.c := by linarith only [f.close]
  let A := C.loU+C.side
  let X := C.c*A-C.s*C.loV
  let Y := C.s*A+C.c*C.loV
  have closed : ClosedInside C X Y := WallProfile.vertex C A C.loV
    ⟨by dsimp only [A]; linarith only [C.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [C.side_pos]⟩
  have first := mul_nonneg cp.le (sub_nonneg.mpr f.lowerU)
  have second := mul_nonneg f.negative.le (sub_nonneg.mpr f.lowerV)
  have excess := mul_pos cp (sub_pos.mpr h.side)
  have gap := mul_pos (show 0<1+C.s by linarith only [f.small])
    (show 0<C.c-(11/25)*(1-C.s) by linarith only [f.close,f.small])
  have xl : -14/25<X := by
    dsimp only [X,A]
    nlinarith only [first,second,excess,gap,C.unit_normal]
  have height : -1<Y := by
    apply lt_of_not_ge
    intro below
    have identity : C.c*X+C.s*Y=A := by
      dsimp only [X,Y]
      linear_combination A*C.unit_normal
    have product := mul_nonneg f.negative.le
      (show 0≤-1-Y by linarith only [below])
    have scaled : C.c*X≤0 := by
      dsimp only [A] at identity
      nlinarith only [identity,product,f.upperU,f.negative]
    have xu : X≤0 := by
      apply le_of_not_gt
      intro positive
      have bad := mul_pos cp positive
      linarith only [scaled,bad]
    exact (not_lt_of_ge below) (above_bar C B X Y closed h.forward xl.le xu
      h.wholeBar h.apartBar)
  have identity : centerY C=Y+C.side*(C.c-C.s)/2 := by
    dsimp only [centerY,Y,A]
    ring
  rw [identity]
  linarith only [height]

/-- A missing positive-successor halfpoint has only the lower-v exit.
The upper-u exit would put the actual foreign C marker in the other
three strict bands and force a width smaller than one. -/
theorem target_lower (C E B : OpenSquare) (h : Input C E B)
    (missing : ¬E.Inside (1/2) (-1)) : -E.c-E.s/2≤E.loV := by
  have eb := normal_bounds h.targetNormal
  have ep : 0<E.c := by linarith only [eb.1]
  have en := h.targetNormal.1
  have order := h.targetNormal.2.1
  have eside : 1<E.side := by simpa only [←h.same] using h.side
  have high : E.c/2-E.s<E.loU+E.side := by
    apply lt_of_not_ge
    intro cap
    have shallow : 13*E.s<3*E.c := by linarith only [cap,h.target.2.1]
    have lower : -(7/20)*(E.c+E.s)≤E.loU := by
      apply le_of_not_gt
      intro low
      apply h.apart (-7/20) (-7/20)
      refine ⟨h.source,?_⟩
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,h.inner.2.1,h.bar0.2.2.1,h.inner.2.2.2,ep,en,shallow]
    linarith only [cap,lower,eside,eb.2.1,en]
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [low,high,h.bar1.1,h.bar1.2.2.2,ep,en]

end N12Compact.C1092MPPMNegativeForward

import Compact.Completion.C1092.MPPMNegativeForwardFaces
import Compact.Completion.C1092.MMMP.EndingAxes

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING section 2. These are the literal
retaining square's points and exclusions. Its missing successor point
and the whole foreign bar are separate inputs to the clearance theorem.
No container wall is substituted for that bar. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
open Completion.OtherCases
set_option Elab.async false
noncomputable section

structure Core (C : OpenSquare) : Prop where
  side : 1<C.side
  normal : Normal C.c (-C.s)
  marker : C.Inside (-7/20) (-7/20)
  ordinary : C.Inside (-1) (-13/50)
  outer : C.Inside (-1) (-2/5)
  forward : C.Inside (-13/50) 0
  halfpoint : C.Inside (-1) (-1/2)
  origin : ¬C.Inside (-1) 0
  corner : ¬C.Inside (-1) (-1)
  northwest : ¬C.Inside (-7/20) (7/20)

structure Faces (C : OpenSquare) : Prop where
  lowerU : -C.c≤C.loU
  lowerV : C.s-C.c≤C.loV
  upperV : C.loV+C.side≤(7/20)*(C.c+C.s)
  negative : C.s<0

theorem faces (C : OpenSquare) (h : Core C) : Faces C := by
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have sn := h.normal.1
  have order := h.normal.2.1
  have lowerU : -C.c≤C.loU := by
    apply le_of_not_gt
    intro low
    apply h.origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.ordinary.2.1,h.outer.2.2.1,h.forward.2.2.2,cp,sn,order]
  have lowerV : C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.halfpoint.1,h.marker.2.1,h.outer.2.2.2,cp,sn,order]
  have upperV : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    apply le_of_not_gt
    intro high
    apply h.northwest
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.ordinary.1,h.forward.2.1,h.forward.2.2.1,cp,sn,order]
  have negative : C.s<0 := by linarith only [lowerU,h.ordinary.1]
  exact ⟨lowerU,lowerV,upperV,negative⟩

/-- Strict source-angle bounds at the complete half-angle endpoint
13/50. These constants are the chapter's rational .873 and .488. -/
theorem narrow_angle {c s : ℝ} (cn : Normal c s) (width : 1<c+(13/50)*s) :
    0<s ∧ 873/1000<c ∧ s<61/125 ∧ c<1 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [width,cb.2.1]
  let x := half c s
  have data := quarter_data c s cp.le cn.1 cn.2.2
  have xp : 0<x := div_pos sp (by linarith only [cp])
  have cosine : (1+x^2)*c=1-x^2 := data.2.2.2.1
  have sine : (1+x^2)*s=2*x := data.2.2.2.2
  have identity : (1+x^2)*(c+(13/50)*s-1)=2*x*(13/50-x) := by
    linear_combination cosine+(13/50)*sine
  have scaled := mul_pos (show 0<1+x^2 by positivity)
    (show 0<c+(13/50)*s-1 by linarith only [width])
  have small : x<13/50 := by
    apply lt_of_not_ge
    intro high
    have bad := mul_nonpos_of_nonneg_of_nonpos xp.le
      (show 13/50-x≤0 by linarith only [high])
    nlinarith only [identity,scaled,bad]
  have square := mul_pos (show 0<13/50-x by linarith only [small])
    (show 0<13/50+x by linarith only [xp])
  have close : 873/1000<c := by
    apply lt_of_not_ge
    intro low
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+x^2 by positivity) (show c-873/1000≤0 by linarith only [low])
    nlinarith only [bad,cosine,square]
  have narrow : s<61/125 := by
    have product := mul_pos (show 0<13/50-x by linarith only [small])
      (show 0<2-(61/125)*(x+13/50) by linarith only [small])
    apply lt_of_not_ge
    intro high
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+x^2 by positivity) (show 61/125-s≤0 by linarith only [high])
    nlinarith only [bad,sine,product]
  have strict : c<1 := by nlinarith only [cn.2.2,sp,cb.2.1,sq_pos_of_pos sp]
  exact ⟨sp,close,narrow,strict⟩

/-- A closed vertex below the bar would meet the same strict foreign
segment. The contact case Y=-1 and both bar endpoints are retained. -/
theorem above_bar (C B : OpenSquare) (X Y : ℝ)
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

structure Cleared (C : OpenSquare) extends Faces C : Prop where
  upperU : C.loU+C.side≤-(13/50)*C.s
  close : 873/1000<C.c
  small : -C.s<61/125
  strictCosine : C.c<1
  vertex : -1<C.s*(C.loU+C.side)+C.c*C.loV

theorem clearance (C B : OpenSquare) (h : Core C)
    (next : ¬C.Inside 0 (-13/50))
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : Cleared C := by
  have f := faces C h
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have upperU : C.loU+C.side≤-(13/50)*C.s := by
    apply le_of_not_gt
    intro high
    apply next
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.ordinary.1,h.ordinary.2.2.1,h.forward.2.2.2,
        cp,h.normal.1,h.normal.2.1]
  have angle := narrow_angle h.normal
    (show 1<C.c+(13/50)*(-C.s) by linarith only [f.lowerU,upperU,h.side])
  have lowerV : -C.c+(14/25)*C.s≤C.loV := by
    apply le_of_not_gt
    intro low
    apply apart (-14/25) (-1)
    refine ⟨?_,bar _ (by norm_num) (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.ordinary.1,h.ordinary.2.2.2,f.lowerU,h.side,
        cp,h.normal.1,h.normal.2.1,cb.2.1,angle.2.2.1]
  let A := C.loU+C.side
  let X := C.c*A-C.s*C.loV
  let Y := C.s*A+C.c*C.loV
  have closed : ClosedInside C X Y := WallProfile.vertex C A C.loV
    ⟨by dsimp only [A]; linarith only [C.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [C.side_pos]⟩
  have first := mul_nonneg cp.le (sub_nonneg.mpr f.lowerU)
  have second := mul_nonneg angle.1.le (sub_nonneg.mpr lowerV)
  have excess := mul_pos cp (sub_pos.mpr h.side)
  have gap := mul_pos (show 0<1+C.s by linarith only [angle.2.2.1])
    (show 0<C.c-(11/25)*(1-C.s) by linarith only [angle.2.1,angle.2.2.1])
  have xl : -14/25<X := by
    dsimp only [X,A]
    nlinarith only [first,second,excess,gap,C.unit_normal]
  have height : -1<Y := by
    apply lt_of_not_ge
    intro below
    have identity : C.c*X+C.s*Y=A := by
      dsimp only [X,Y]
      linear_combination A*C.unit_normal
    have product := mul_nonneg angle.1.le
      (show 0≤-1-Y by linarith only [below])
    have scaled : C.c*X≤0 := by
      dsimp only [A] at identity
      nlinarith only [identity,product,upperU,angle.1]
    have xu : X≤0 := by
      apply le_of_not_gt
      intro positive
      have bad := mul_pos cp positive
      linarith only [scaled,bad]
    exact (not_lt_of_ge below) (above_bar C B X Y closed h.forward xl.le xu bar apart)
  exact ⟨f,upperU,angle.2.1,angle.2.2.1,angle.2.2.2,height⟩

structure SuccessorFaces (E : OpenSquare) : Prop where
  lowerV : -E.c≤E.loV
  upperU : E.loU+E.side≤E.c-E.s
  anchorU : E.loU<-(13/50)*E.s
  lowerU : -(7/20)*(E.c+E.s)≤E.loU

/-- A literal quarter turn of the same square, with no reflected or
independently chosen recipient pose. -/
theorem successor_faces (D : OpenSquare) (h : Core D) :
    SuccessorFaces (C1092MMMPEndingAxes.clockwise D) := by
  have f := faces D h
  constructor
  · exact f.lowerU
  · change -D.loV≤D.c-D.s
    linarith only [f.lowerV]
  · change -D.loV-D.side<-(13/50)*D.s
    linarith only [h.forward.2.2.2]
  · change -(7/20)*(D.c+D.s)≤-D.loV-D.side
    linarith only [f.upperV]

end
#print axioms faces
#print axioms clearance
#print axioms successor_faces
end N12Compact.C1092MPPMAllNonpositive

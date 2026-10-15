import Compact.Completion.C1092.MPPMInwardFinalScalars
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import Compact.Geometry.ClosedPointExclusion

/-! OPPOSED-MISSING-INWARD §1. The bottom segment belongs to one
actual B, including its endpoints; its strict interior excludes even
a tangent closed vertex of C. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
open Completion.OtherCases
set_option Elab.async false

structure MissingProfile (C : OpenSquare) : Prop where
  side : 1<C.side
  normal : Normal C.c (-C.s)
  negative : C.s<0
  close : 17/20<C.c
  small : -C.s<13/25
  marker : C.Inside (-7/20) (-7/20)
  inner : C.Inside 0 (-13/50)
  forward : C.Inside (-13/50) 0
  outer : C.Inside (-1) (-2/5)
  lowerU : -C.c-(13/50)*C.s≤C.loU
  lowerV : -C.c+(2/5)*C.s≤C.loV
  upperV : C.loV+C.side≤0
  bottomExit : (-C.c+(13/50)*C.s≤C.loV ∧ C.side≤C.c-(13/50)*C.s) ∨
    C.loU+C.side≤-(13/50)*C.c-C.s

private theorem above_bar (C B : OpenSquare) (X Y : ℝ)
    (closed : ClosedInside C X Y) (inner : C.Inside 0 (-13/50))
    (xl : -14/25≤X) (xu : X≤0)
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : -1<Y := by
  apply lt_of_not_ge
  intro below
  by_cases equal : Y= -1
  · have vertex : ClosedInside C X (-1) := by simpa only [equal] using closed
    exact ClosedPointExclusion.outside_of_closed B C X (-1)
      (fun x y own => apart x y ⟨own.2,own.1⟩) vertex (bar X xl xu)
  · have strict : Y< -1 := lt_of_le_of_ne below equal
    let t := (-1-Y)/(-13/50-Y)
    have den : 0< -13/50-Y := by linarith only [strict]
    have positive : 0<t := div_pos (by linarith only [strict]) den
    have small : t<1 := (div_lt_one den).mpr (by norm_num)
    have relation : t*(-13/50-Y)= -1-Y := div_mul_cancel₀ _ den.ne'
    have coordinate : (1-t)*Y+t*(-13/50)= -1 := by nlinarith only [relation]
    have low : -14/25≤(1-t)*X+t*0 := by
      have product := mul_nonneg (show 0≤1-t by linarith only [small])
        (show 0≤X+14/25 by linarith only [xl])
      nlinarith only [product,positive]
    have high : (1-t)*X+t*0≤0 := by
      have product := mul_nonpos_of_nonneg_of_nonpos
        (show 0≤1-t by linarith only [small]) xu
      nlinarith only [product]
    have own := WallProfile.strict_closed_segment C X Y 0 (-13/50) t
      closed inner positive small
    rw [coordinate] at own
    exact apart _ _ ⟨own,bar _ low high⟩

/-- Division-free form of the exact geometric floor h₀(p). -/
theorem missing_floor (C B : OpenSquare) (h : MissingProfile C)
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) :
    C.c-1-C.s*(1-C.c-(13/50)*C.s)<C.c*(C.loV+C.side) := by
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [h.close]
  have sp : 0< -C.s := by linarith only [h.negative]
  let A := C.loU+C.side
  let X := C.c*A-C.s*C.loV
  let Y := C.s*A+C.c*C.loV
  have closed : ClosedInside C X Y := WallProfile.vertex C A C.loV
    ⟨by dsimp [A]; linarith only [C.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [C.side_pos]⟩
  have first := mul_nonneg cp.le (sub_nonneg.mpr h.lowerU)
  have last := mul_nonneg sp.le (sub_nonneg.mpr h.lowerV)
  have strict := mul_pos cp (sub_pos.mpr h.side)
  have half : -C.c*C.s≤1/2 := by nlinarith only [C.unit_normal,sq_nonneg (C.c+C.s)]
  have xl : -14/25<X := by
    dsimp [X,A]
    nlinarith only [first,last,strict,C.unit_normal,half,h.close,sq_nonneg C.s]
  have xu : X<0 := by
    rcases h.bottomExit with width|cap
    · have bound := mul_pos cp
        (show 0<C.side-C.c-(2/5)*C.s-A by
          dsimp [A]; linarith only [h.outer.1])
      have floor := mul_nonneg sp.le
        (show 0≤-C.side-C.loV by linarith only [h.upperV])
      have product := mul_nonneg
        (show 0≤C.c+C.s by linarith only [h.close,h.small])
        (show 0≤C.c-(13/50)*C.s-C.side by linarith only [width.2])
      have cs := mul_pos cp sp
      dsimp [X,A] at *
      nlinarith only [bound,floor,product,cs,sq_nonneg C.s]
    · have bound := mul_nonneg cp.le
        (show 0≤-(13/50)*C.c-C.s-A by exact sub_nonneg.mpr cap)
      have floor := mul_nonneg sp.le
        (show 0≤-C.side-C.loV by linarith only [h.upperV])
      have gap := mul_pos sp (show 0<C.side-C.c by linarith only [h.side,cb.2.1])
      dsimp [X,A] at *
      nlinarith only [bound,floor,gap,sq_nonneg C.c]
  have above := above_bar C B X Y closed h.inner xl.le xu.le bar apart
  have lower := mul_nonneg sp.le (sub_nonneg.mpr h.lowerU)
  have excess := mul_pos (show 0<C.c-C.s by linarith only [cp,sp]) (sub_pos.mpr h.side)
  dsimp [Y,A] at above
  nlinarith only [above,lower,excess]

theorem floor_coarse {c s H : ℝ} (cn : Normal c s) (close : 17/20<c)
    (small : s<13/25) (floor : c-1+s*(1-c+(13/50)*s)<c*H) : -1/25<H := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [close]
  have den : 0<1+c := by linarith only [cp]
  let B := c-1+s*(1-c+(13/50)*s)
  have identity : (1+c)*B=s^2*((13/50)*(1+c)-1+s) := by
    dsimp [B]
    linear_combination (1-s)*cn.2.2
  have base : 629/10000<(1/25)*c*(1+c) := by
    have product := mul_pos (show 0<c-17/20 by linarith only [close])
      (show 0<c+37/20 by linarith only [cp])
    nlinarith only [product]
  have positive : 0<(1+c)*(B+c/25) := by
    by_cases low : s≤1/3
    · have square := mul_nonneg (show 0≤1/3-s by linarith only [low])
        (show 0≤1/3+s by linarith only [cn.1])
      have coefficient := mul_nonneg (sq_nonneg s)
        (show 0≤(13/50)*(1+c)-1+s+519/1000 by linarith only [close,cn.1])
      nlinarith only [identity,base,square,coefficient]
    · have square := mul_nonneg (show 0≤13/25-s by linarith only [small])
        (show 0≤13/25+s by linarith only [cn.1])
      have coefficient := mul_nonneg (sq_nonneg s)
        (show 0≤(13/50)*(1+c)-1+s+557/3000 by linarith only [close,low])
      nlinarith only [identity,base,square,coefficient]
  have bound : 0<B+c/25 := pos_of_mul_pos_right positive den.le
  apply lt_of_not_ge
  intro no
  have bad := mul_nonpos_of_nonneg_of_nonpos cp.le
    (show H+1/25≤0 by linarith only [no])
  dsimp [B] at bound
  nlinarith only [bound,floor,bad]

theorem missing_near_center (C : OpenSquare) (h : MissingProfile C)
    (floor : C.c-1-C.s*(1-C.c-(13/50)*C.s)<C.c*(C.loV+C.side)) :
    -(1/25)<C.loV+C.side ∧ C.Inside (-1/25) (-1/25) := by
  have height := floor_coarse h.normal h.close h.small (by nlinarith only [floor])
  have cb := normal_bounds h.normal
  refine ⟨height,?_,?_,?_,?_⟩
  · linarith only [h.outer.1,h.close,h.small]
  · linarith only [h.lowerU,h.side,cb.2.1,h.normal.1,h.normal.2.1]
  · linarith only [h.upperV,h.side,cb.2.2.2.2.2]
  · linarith only [height,cb.2.2.2.2.1]

#print axioms missing_floor
#print axioms missing_near_center
end N12Compact.C1092MPPMInwardFinal

import Compact.Completion.C1092.MPPMOnePositiveScalars
import Compact.Completion.C1092.MPPMAllNonpositiveCore
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry

/-! ONE-POSITIVE-CONTINUOUS-ENDING Lemma 2, literal physical input
and clearance. The foreign crosspoint, whole actual bottom bar and the
same C are retained through the lowest-vertex and support argument. -/
namespace N12Compact.C1092MPPMOnePositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports Completion.OtherCases
set_option Elab.async false
noncomputable section

structure PositiveMissingInput (C E B : OpenSquare) : Prop where
  source : C1092MPPMAllNonpositive.Core C
  same : C.side=E.side
  close : 97/100<C.c
  small : 4*(-C.s)<C.c
  height : C.loV+C.side<43/500
  recipient : Normal E.c E.s
  marker : E.Inside (7/20) (-7/20)
  crosspoint : E.Inside 0 (-1/2)
  lowerV : -E.c-E.s≤E.loV
  upperU : E.loU+E.side≤E.c-(14/25)*E.s
  large : 13/87≤C1092MPPMCrosspointSupport.half E.c E.s
  bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1)
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)
  apartBar : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)

theorem positive_missing_clearance (C E B : OpenSquare) (h : PositiveMissingInput C E B) :
    C.loU+C.side≤-C.s/2 ∧ -1<C.s*(C.loU+C.side)+C.c*C.loV := by
  have f := C1092MPPMAllNonpositive.faces C h.source
  have cb := normal_bounds h.source.normal
  have cp : 0<C.c := by linarith only [h.close]
  have sp : 0< -C.s := by linarith only [f.negative]
  have small : -C.s<1/4 := by linarith only [h.small,cb.2.1]
  have cap : C.loU+C.side≤-C.s/2 := by
    apply le_of_not_gt
    intro high
    apply h.apart 0 (-1/2)
    refine ⟨?_,h.crosspoint⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,h.source.ordinary.1,h.source.forward.2.2.2,
        f.upperV,h.source.side,cb.2.1,cp,sp,h.source.normal.2.1]
  have lowerV : -C.c+(14/25)*C.s≤C.loV := by
    apply le_of_not_gt
    intro low
    apply h.apartBar (-14/25) (-1)
    refine ⟨?_,h.bar _ (by norm_num) (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,h.source.ordinary.1,h.source.ordinary.2.2.2,
        f.lowerU,h.source.side,cb.2.1,cp,sp,small,h.source.normal.2.1]
  let A := C.loU+C.side
  let X := C.c*A-C.s*C.loV
  let Y := C.s*A+C.c*C.loV
  have closed : FourSquareAnchors.ClosedInside C X Y := WallProfile.vertex C A C.loV
    ⟨by dsimp [A]; linarith only [C.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [C.side_pos]⟩
  have first := mul_nonneg cp.le (sub_nonneg.mpr f.lowerU)
  have second := mul_nonneg sp.le (sub_nonneg.mpr lowerV)
  have excess := mul_pos cp (sub_pos.mpr h.source.side)
  have cross := mul_nonneg sp.le (show 0≤1-C.c by linarith only [cb.2.1])
  have xl : -14/25<X := by
    dsimp [X,A]
    nlinarith only [first,second,excess,cross,h.close,small,C.unit_normal,sq_nonneg C.s]
  have height : -1<Y := by
    apply lt_of_not_ge
    intro below
    have identity : C.c*X+C.s*Y=A := by
      dsimp [X,Y]
      linear_combination A*C.unit_normal
    have product := mul_nonneg sp.le (show 0≤-1-Y by linarith only [below])
    have scaled : C.c*X≤0 := by dsimp [A] at identity; nlinarith only [identity,product,cap,sp]
    have xu : X≤0 := by
      apply le_of_not_gt
      intro bad
      have positive := mul_pos cp bad
      linarith only [scaled,positive]
    exact (not_lt_of_ge below) (C1092MPPMAllNonpositive.above_bar C B X Y closed
      h.source.forward xl.le xu h.bar h.apartBar)
  exact ⟨cap,height⟩

theorem positive_missing_upward (C E B : OpenSquare) (h : PositiveMissingInput C E B) :
    -E.s/2<upper C E.c E.s := by
  have f := C1092MPPMAllNonpositive.faces C h.source
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := E.s
  let k := c*d-s*t
  let ell := c*t+s*d
  have cp : 0<c := by dsimp [c]; linarith only [h.close]
  have sp : 0<s := by dsimp [s]; linarith only [f.negative]
  have cb := normal_bounds h.source.normal
  have small : s<1/4 := by dsimp [s]; linarith only [h.small,cb.2.1]
  have dp : 0<d := by dsimp [d]; linarith only [(normal_bounds h.recipient).1]
  have tn : 0≤t := h.recipient.1
  have kp : 0<k := by
    have first := mul_pos dp (show 0<c-s by dsimp [c]; linarith only [h.close,small])
    have last := mul_nonneg sp.le (sub_nonneg.mpr h.recipient.2.1)
    dsimp [k]
    nlinarith only [first,last]
  have ep : 0<ell := by
    have first := mul_pos sp dp
    have last := mul_nonneg cp.le tn
    dsimp [ell]
    nlinarith only [first,last]
  have strictCosine : c<1 := by nlinarith only [h.source.normal.2.2,sp,sq_pos_of_pos sp,cb.2.1]
  have vertex := (positive_missing_clearance C E B h).2
  have floor : -1+C.side*(c+s)/2<centerY C := by
    dsimp [centerY,c,s] at *
    nlinarith only [vertex]
  have support : upper C E.c E.s=d*centerX C+t*centerY C+C.side*(k+ell)/2 := by
    dsimp [upper,supportRadius]
    rw [show E.c*C.c+E.s*C.s=k by dsimp [k,c,s,d,t]; ring,
      show -E.c*C.s+E.s*C.c=ell by dsimp [ell,c,s,d,t]; ring,
      abs_of_nonneg kp.le,abs_of_nonneg ep.le]
    dsimp [d,t]
    ring
  have coordinate : c*centerX C-s*centerY C=C.loU+C.side/2 := by
    have original := (center_coordinates C).1
    dsimp [c,s]
    linarith only [original]
  have low := mul_nonneg dp.le (show 0≤C.loU+c by dsimp [c]; linarith only [f.lowerU])
  have raised := mul_pos ep (sub_pos.mpr floor)
  have coefficient : 0<ell*(c+s)+d+c*(k+ell) := by positivity
  have excess := mul_pos (sub_pos.mpr h.source.side) coefficient
  have identity : -c*d-ell+(ell*(c+s)+d+c*(k+ell))/2=
      (1-c)*(d*(1-s)-c*t) := by
    dsimp [k,ell]
    linear_combination (d/2)*h.source.normal.2.2
  have first := mul_pos (mul_pos (sub_pos.mpr strictCosine) dp)
    (show 0<1-s by linarith only [small])
  have last := mul_nonneg (mul_nonneg cp.le tn)
    (show 0≤c-1/2 by dsimp [c]; linarith only [h.close])
  have scaledSupport := congrArg (fun x : ℝ => c*x) support
  have scaledCoordinate := congrArg (fun x : ℝ => d*x) coordinate
  have scaled : 0<c*(upper C E.c E.s+t/2) := by
    nlinarith only [scaledSupport,scaledCoordinate,low,raised,excess,identity,first,last]
  have positive := pos_of_mul_pos_right scaled cp.le
  dsimp [t] at positive
  linarith only [positive]

end
#print axioms positive_missing_clearance
#print axioms positive_missing_upward
end N12Compact.C1092MPPMOnePositive

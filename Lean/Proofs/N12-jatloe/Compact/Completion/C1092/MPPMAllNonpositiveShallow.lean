import Compact.Completion.C1092.MPPMAllNonpositivePredecessor

/-! ALL-NEGATIVE-MIXED-FORWARD-ENDING section 5.3. The hypothetical
large source angle forces a real origin face. Only in that range is the
lowest vertex compared with the complete actual foreign bar. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot C977CornerCubic FourSquareAnchors
open Completion.OtherCases
set_option Elab.async false
noncomputable section

structure Shallow (C : OpenSquare) : Prop where
  slope : 4*(-C.s)<C.c
  close : 97/100<C.c
  small : -C.s<1/4
  height : C.loV+C.side<43/500

/-- A retaining negative square with an actual missing predecessor is
strictly shallower than slope 1/4. There is no successor membership or
angle premise, so this is also the one-positive chapter's local Lemma 1. -/
theorem predecessor_shallow (C W B : OpenSquare) (h : Core C) (w : MissingPredecessor W)
    (same : C.side=W.side) (marker : W.Inside (-7/20) (7/20))
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y))
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apartBar : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : Shallow C := by
  let c := C.c
  let s := -C.s
  let A := C.loU+C.side
  let H := C.loV+C.side
  have cn : Normal c s := h.normal
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have f := faces C h
  have sp : 0<s := by dsimp only [s]; linarith only [f.negative]
  have cap : H<(43/500)*c-(12/25)*s := by
    simpa only [H,c,s,mul_neg,sub_neg_eq_add] using
      predecessor_cap C W h w same marker apart
  have anchor : -(13/50)*s<H := by
    dsimp only [H,s]
    linarith only [h.forward.2.2.2]
  have coarse := preliminary_angle cn anchor cap
  have slope : 4*s<c := by
    apply lt_of_not_ge
    intro high
    have Hnegative : H<0 := by linarith only [cap,high,cp]
    have upperU : A≤s := by
      apply le_of_not_gt
      intro highU
      apply apartBar 0 (-1)
      refine ⟨?_,bar 0 (by norm_num) (by norm_num)⟩
      refine ⟨?_,?_,?_,?_⟩ <;>
        dsimp only [A,H,c,s] at highU Hnegative coarse cb cp ⊢ <;>
        linarith only [highU,Hnegative,h.ordinary.1,h.ordinary.2.2.2,
          h.side,cb.2.1,coarse.1,cp,h.normal.1]
    let X := c*A+s*C.loV
    let Y := -s*A+c*C.loV
    have closed : ClosedInside C X Y := by
      convert WallProfile.vertex C A C.loV
        ⟨by dsimp only [A]; linarith only [C.side_pos],le_rfl⟩
        ⟨le_rfl,by linarith only [C.side_pos]⟩ using 1 <;>
        dsimp only [X,Y,c,s] <;> ring
    have first := mul_nonneg cp.le (sub_nonneg.mpr f.lowerU)
    have second := mul_nonneg sp.le (sub_nonneg.mpr f.lowerV)
    have excess := mul_pos cp (sub_pos.mpr h.side)
    have square := mul_nonneg sp.le (show 0≤1-c by linarith only [cb.2.1])
    have xl : -14/25<X := by
      dsimp only [X,A,c,s] at *
      nlinarith only [first,second,excess,square,C.unit_normal,coarse.2.1,coarse.2.2]
    have height : -1<Y := by
      apply lt_of_not_ge
      intro below
      have identity : c*X-s*Y=A := by
        dsimp only [X,Y]
        linear_combination A*cn.2.2
      have product := mul_nonneg sp.le (show 0≤-1-Y by linarith only [below])
      have scaled : c*X≤0 := by nlinarith only [identity,product,upperU]
      have xu : X≤0 := by
        apply le_of_not_gt
        intro positive
        have bad := mul_pos cp positive
        linarith only [scaled,bad]
      exact (not_lt_of_ge below) (above_bar C B X Y closed h.forward xl.le xu bar apartBar)
    have lowerA : C.side-c≤A := by
      dsimp only [A,c]
      linarith only [f.lowerU]
    have weight := mul_le_mul_of_nonneg_left lowerA sp.le
    have sideExcess := mul_pos (sub_pos.mpr h.side)
      (show 0<c+s by linarith only [cp,sp])
    have capWeight := mul_lt_mul_of_pos_left cap cp
    have margin := heightGap_positive cn coarse.2.1 coarse.2.2 high
    dsimp only [Y,H,heightGap] at height capWeight margin
    nlinarith only [height,weight,sideExcess,capWeight,margin]
  have product := mul_pos (show 0<c-4*s by linarith only [slope])
    (show 0<c+4*s by linarith only [cp,sp])
  have close : 97/100<c := by
    apply lt_of_not_ge
    intro low
    have square := mul_nonneg (show 0≤97/100-c by linarith only [low])
      (show 0≤97/100+c by linarith only [cp])
    nlinarith only [product,square,cn.2.2]
  exact ⟨slope,close,by linarith only [slope,cb.2.1],
    by change H<43/500; linarith only [cap,cb.2.1,cn.1]⟩

end
#print axioms predecessor_shallow
end N12Compact.C1092MPPMAllNonpositive

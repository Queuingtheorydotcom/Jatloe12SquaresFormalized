import Compact.Completion.OtherCases.C976LeftTop.Scalars
import Mathlib.Data.Real.Sqrt

/-! The two one-angle inequalities f0,f1 in C976-LEFT-TOP-ANGLE section5.
Coarse exact rational bounds suffice for f0. For f1 the manuscript's
monotonicity is the two-point unit-circle difference at (11,8)/sqrt(185).
No angle samples, derivative assumptions or new certificate are used.
Source only; not compiled. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.Scalars
set_option Elab.async false

theorem left_low_margin (l h : ℝ) (lp : 0 < l) (hp : 0 < h)
    (unit : l^2+h^2=1) (low : (1/3)*l ≤ h) (high : h ≤ l/2) :
    0 < (37/100)*l+(11/100)*h-189/625-(169/5000)*l^2-(39/625)*l*h := by
  have first := mul_nonneg (show 0 ≤ 3*h-l by linarith only [low])
    (show 0 ≤ 3*h+l by linarith only [lp,hp])
  have last := mul_nonneg (show 0 ≤ l-2*h by linarith only [high])
    (show 0 ≤ l+2*h by linarith only [lp,hp])
  have lSquare : 4/5 ≤ l^2 := by nlinarith only [unit,last]
  have hSquare : 1/10 ≤ h^2 := by nlinarith only [unit,first]
  have lUpper : l^2 ≤ 9/10 := by linarith only [unit,hSquare]
  have cross := mul_nonneg (show 0 ≤ l-2*h by linarith only [high])
    (show 0 ≤ 2*l-h by linarith only [high,lp])
  have product : l*h ≤ 2/5 := by nlinarith only [unit,cross]
  have lLower : 89/100 < l := by
    apply lt_of_not_ge
    intro small
    have square := mul_nonneg (show 0 ≤ 89/100-l by linarith only [small])
      (show 0 ≤ 89/100+l by linarith only [lp])
    nlinarith only [square,lSquare]
  have hLower : 31/100 < h := by
    apply lt_of_not_ge
    intro small
    have square := mul_nonneg (show 0 ≤ 31/100-h by linarith only [small])
      (show 0 ≤ 31/100+h by linarith only [hp])
    nlinarith only [square,hSquare]
  nlinarith only [lLower,hLower,lUpper,product]

private def f1 (l h : ℝ) : ℝ :=
  (37/100)*l+(11/100)*h-219/625+(17/625)*l^2-(161/2500)*l*h

private theorem high_endpoint :
    ∃ L H : ℝ, 0 < L ∧ 0 < H ∧ L^2+H^2=1 ∧ H=(8/11)*L ∧ 0 < f1 L H := by
  let d : ℝ := Real.sqrt 185
  have dp : 0 < d := Real.sqrt_pos.2 (by norm_num)
  have ds : d^2=185 := Real.sq_sqrt (by norm_num)
  have dn : d ≠ 0 := ne_of_gt dp
  have cube := congrArg (fun x : ℝ => x*d) ds
  have margin : 1344/99 < d := by nlinarith only [ds,dp]
  refine ⟨11/d,8/d,div_pos (by norm_num) dp,div_pos (by norm_num) dp,?_,?_,?_⟩
  · field_simp [dn]
    nlinarith only [ds]
  · ring
  · have identity : f1 (11/d) (8/d)=(99*d-1344)/3700 := by
      dsimp only [f1]
      field_simp [dn]
      nlinarith only [ds,cube]
    rw [identity]
    exact div_pos (by linarith only [margin]) (by norm_num)

theorem left_high_margin (l h : ℝ) (lp : 0 < l) (hp : 0 < h)
    (unit : l^2+h^2=1) (low : l/2 ≤ h) (high : h ≤ (8/11)*l) :
    0 < (37/100)*l+(11/100)*h-219/625+(17/625)*l^2-(161/2500)*l*h := by
  obtain ⟨L,H,Lp,Hp,endpoint,ratio,positive⟩ := high_endpoint
  have cross : L*h ≤ H*l := by
    have weighted := mul_nonneg Lp.le (sub_nonneg.mpr high)
    nlinarith only [weighted,ratio]
  have sineOrder : h ≤ H := by
    apply le_of_not_gt
    intro large
    have square := mul_pos (sub_pos.mpr large) (add_pos hp Hp)
    have cosineOrder : l < L := by nlinarith only [unit,endpoint,square,lp,Lp]
    have first := mul_pos Lp (sub_pos.mpr large)
    have last := mul_pos Hp (sub_pos.mpr cosineOrder)
    nlinarith only [first,last,cross]
  have cosineOrder : L ≤ l := by
    apply le_of_not_gt
    intro small
    have square := mul_pos (sub_pos.mpr small) (add_pos lp Lp)
    have sineSquare := mul_nonneg (sub_nonneg.mpr sineOrder) (add_pos hp Hp).le
    nlinarith only [unit,endpoint,square,sineSquare]
  have circle : (l+L)*(l-L)=(H-h)*(h+H) := by
    nlinarith only [unit,endpoint]
  have slopeSum : (l+L)/2 ≤ h+H := by linarith only [low,ratio,Lp]
  have weighted := mul_nonneg (sub_nonneg.mpr sineOrder) (sub_nonneg.mpr slopeSum)
  have scaled : (l+L)*((H-h)/2) ≤ (l+L)*(l-L) := by
    nlinarith only [circle,weighted]
  have step : (H-h)/2 ≤ l-L :=
    (mul_le_mul_left (add_pos lp Lp)).mp scaled
  have hUpper : h ≤ 1 := by nlinarith only [unit,sq_nonneg l,sq_nonneg (h-1),hp]
  let A := 37/100+(17/625)*(l+L)-(161/2500)*h
  let B := 11/100-(161/2500)*L
  have aBound : 3/10 ≤ A := by dsimp only [A]; linarith only [hUpper,lp,Lp]
  have bBound : B ≤ 11/100 := by dsimp only [B]; linarith only [Lp]
  have first := mul_nonneg (sub_nonneg.mpr cosineOrder) (sub_nonneg.mpr aBound)
  have last := mul_nonneg (sub_nonneg.mpr sineOrder) (sub_nonneg.mpr bBound)
  have identity : f1 l h-f1 L H=(l-L)*A-(H-h)*B := by
    dsimp only [f1,A,B]
    ring
  have result : 0 < f1 l h := by
    nlinarith only [identity,first,last,step,sineOrder,positive]
  exact result

end N12Compact.Completion.OtherCases.C976LeftTop.Scalars

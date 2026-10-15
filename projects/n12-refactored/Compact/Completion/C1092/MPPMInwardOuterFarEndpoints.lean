import Compact.Completion.C1092.MPPMInwardOuterFarScalars

/-! The two exact rational quartic endpoint estimates for the complete
closed source half-angle intervals. Finite differences replace the
displayed derivative inequalities in the two manuscripts. -/
namespace N12Compact.C1092MPPMInwardOuterFar
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

private theorem quartic_lower (a0 a1 a2 a3 a4 x v : ℝ)
    (a2n : 0≤a2) (a3n : 0≤a3) (a4n : 0≤a4)
    (xn : 0≤x) (order : x≤v) (slope : 0≤a1-2*a2*v-3*a3*v^2) :
    a0-a1*v+a2*v^2+a3*v^3-a4*v^4≤
      a0-a1*x+a2*x^2+a3*x^3-a4*x^4 := by
  have vn : 0≤v := xn.trans order
  have square := mul_nonneg (sub_nonneg.mpr order) (add_nonneg vn xn)
  have mixed := mul_nonneg vn (sub_nonneg.mpr order)
  have first := mul_nonneg a2n (show 0≤2*v-(x+v) by linarith only [order])
  have last := mul_nonneg a3n
    (show 0≤3*v^2-(x^2+x*v+v^2) by nlinarith only [square,mixed])
  have fourth := mul_nonneg a4n
    (show 0≤x^3+x^2*v+x*v^2+v^3 by positivity)
  have bracket : 0≤a1-a2*(x+v)-a3*(x^2+x*v+v^2)+
      a4*(x^3+x^2*v+x*v^2+v^3) := by
    nlinarith only [slope,first,last,fourth]
  have product := mul_nonneg (sub_nonneg.mpr order) bracket
  have identity :
      (a0-a1*x+a2*x^2+a3*x^3-a4*x^4)-
        (a0-a1*v+a2*v^2+a3*v^3-a4*v^4)=
      (v-x)*(a1-a2*(x+v)-a3*(x^2+x*v+v^2)+
        a4*(x^3+x^2*v+x*v^2+v^3)) := by ring
  linarith only [product,identity]

private theorem coordinate_form {c s : ℝ} (cn : Normal c s) :
    c=(1-(half c s)^2)/(1+(half c s)^2) ∧
      s=2*(half c s)/(1+(half c s)^2) := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have den : 0<1+(half c s)^2 := by positivity
  exact ⟨(eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1]),
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])⟩

theorem missing_endpoint {c s : ℝ} (cn : Normal c s)
    (cap : half c s≤279/1000) :
    0<recipientGap 0 c s (275/373) (252/373) := by
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [(normal_bounds cn).1])
  have lower := quartic_lower 2450 10175 12602 7875 23900 x (279/1000)
    (by norm_num) (by norm_num) (by norm_num) xn cap (by norm_num)
  have numerator : 0<2450-10175*x+12602*x^2+7875*x^3-23900*x^4 := by
    norm_num at lower
    linarith only [lower]
  have coords := coordinate_form cn
  have cf : c=(1-x^2)/(1+x^2) := coords.1
  have sf : s=2*x/(1+x^2) := coords.2
  have den : 0<1+x^2 := by positivity
  have identity : 9325*(1+x^2)^2*recipientGap 0 c s (275/373) (252/373)=
      2450-10175*x+12602*x^2+7875*x^3-23900*x^4 := by
    rw [cf,sf]
    dsimp only [recipientGap,alpha]
    field_simp [den.ne'] <;> ring
  have weighted : 0<9325*(1+x^2)^2*recipientGap 0 c s (275/373) (252/373) := by
    rw [identity]
    exact numerator
  exact pos_of_mul_pos_right weighted (by positivity)

theorem centered_endpoint {c s : ℝ} (cn : Normal c s)
    (cap : half c s≤21/100) :
    0<recipientGap (17/125) c s (275/373) (252/373) := by
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [(normal_bounds cn).1])
  have lower := quartic_lower 7966 41525 63010 48725 115216 x (21/100)
    (by norm_num) (by norm_num) (by norm_num) xn cap (by norm_num)
  have numerator : 0<7966-41525*x+63010*x^2+48725*x^3-115216*x^4 := by
    norm_num at lower
    linarith only [lower]
  have coords := coordinate_form cn
  have cf : c=(1-x^2)/(1+x^2) := coords.1
  have sf : s=2*x/(1+x^2) := coords.2
  have den : 0<1+x^2 := by positivity
  have identity : 46625*(1+x^2)^2*recipientGap (17/125) c s (275/373) (252/373)=
      7966-41525*x+63010*x^2+48725*x^3-115216*x^4 := by
    rw [cf,sf]
    dsimp only [recipientGap,alpha]
    field_simp [den.ne'] <;> ring
  have weighted : 0<46625*(1+x^2)^2*recipientGap (17/125) c s (275/373) (252/373) := by
    rw [identity]
    exact numerator
  exact pos_of_mul_pos_right weighted (by positivity)

private theorem recipient_expand (eta c s d t : ℝ) :
    recipientGap eta c s d t=
      1-(1-c*alpha c s+(1-eta)*s)*d-
        (1-s*alpha c s-(1-eta)*c)*t := by
  dsimp [recipientGap]
  ring

theorem missing_recipient_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (cap : half c s≤279/1000) (far : 7/18<half d t) :
    0<recipientGap 0 c s d t := by
  have cb := normal_bounds cn
  have coords := cap_coordinates cn (by norm_num : (0:ℝ)≤279/1000) (by norm_num) cap
  have close : 17/20<c := by nlinarith only [coords.1]
  have small : s<13/25 := by nlinarith only [coords.2]
  have an : 0≤alpha c s := by dsimp [alpha]; linarith only [cb.2.1,cn.1]
  have au : alpha c s<29/100 := by dsimp [alpha]; linarith only [close,small]
  let A := 1-c*alpha c s+s
  let B := 1-s*alpha c s-c
  have first := mul_nonneg an (show 0≤1-c by linarith only [cb.2.1])
  have last := mul_nonneg cn.1 an
  have Ab : 71/100<A := by dsimp [A]; nlinarith only [first,au,cn.1]
  have Bb : B<3/20 := by dsimp [B]; nlinarith only [last,close]
  have compare := recipient_order en (far_coordinates en far).1.le
    (show 0≤A by linarith only [Ab])
    (show 0≤(252/373)*A-(275/373)*B by linarith only [Ab,Bb])
  have endpoint := missing_endpoint cn cap
  rw [recipient_expand] at endpoint ⊢
  dsimp only [A,B] at compare
  nlinarith only [endpoint,compare]

theorem centered_recipient_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (cap : half c s≤21/100) (far : 7/18<half d t) :
    0<recipientGap (17/125) c s d t := by
  have cb := normal_bounds cn
  have coords := cap_coordinates cn (by norm_num : (0:ℝ)≤21/100) (by norm_num) cap
  have close : 91/100<c := by nlinarith only [coords.1]
  have small : s<41/100 := by nlinarith only [coords.2]
  have an : 0≤alpha c s := by dsimp [alpha]; linarith only [cb.2.1,cn.1]
  have au : alpha c s<1/5 := by dsimp [alpha]; linarith only [close,small]
  let A := 1-c*alpha c s+(108/125)*s
  let B := 1-s*alpha c s-(108/125)*c
  have first := mul_nonneg an (show 0≤1-c by linarith only [cb.2.1])
  have last := mul_nonneg cn.1 an
  have Ab : 4/5<A := by dsimp [A]; nlinarith only [first,au,cn.1]
  have Bb : B<107/500 := by dsimp [B]; nlinarith only [last,close]
  have compare := recipient_order en (far_coordinates en far).1.le
    (show 0≤A by linarith only [Ab])
    (show 0≤(252/373)*A-(275/373)*B by linarith only [Ab,Bb])
  have endpoint := centered_endpoint cn cap
  rw [recipient_expand] at endpoint ⊢
  dsimp only [A,B] at compare
  nlinarith only [endpoint,compare]

end
end N12Compact.C1092MPPMInwardOuterFar

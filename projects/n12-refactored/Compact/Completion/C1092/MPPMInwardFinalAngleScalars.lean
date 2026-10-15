import Compact.Completion.C1092.MPPMInwardFinalCapScalars

/-! The endpoint and coefficient norms of CENTERED-NEGATIVE-INWARD-ANGLE.
The inequalities hold on whole canonical arcs, including equality at
half-angle 21/100 and every relative-angle transition. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars CommonCases.CanonicalProjection
set_option Elab.async false

theorem canonical_half_bounds {c s : ℝ} (cn : Normal c s) :
    0≤half c s ∧ half c s≤5/12 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have den : 0≤1+x^2 := by nlinarith only [sq_nonneg x]
  have order := mul_nonneg den (sub_nonneg.mpr cn.2.1)
  refine ⟨data.1,?_⟩
  apply le_of_not_gt
  intro no
  have square := mul_nonneg (show 0≤x-5/12 by linarith only [no])
    (show 0≤x+5/12 by linarith only [data.1])
  nlinarith only [order,data.2.2.2.1,data.2.2.2.2,square,no]

theorem angle_endpoint {c s : ℝ} (cn : Normal c s) (low : 21/100≤half c s) :
    c≤9559/10441 ∧ (7/16)*c≤s ∧ (2/5)*c≤s ∧ 13/10<c+s ∧ 0<1-(543/500)*c := by
  have cb := normal_bounds cn
  have endpoint : Normal (9559/10441) (4200/10441) := by norm_num [Normal]
  have endpointHalf : half (9559/10441) (4200/10441)=(21:ℝ)/100 := by norm_num [half]
  have cross := half_cross endpoint cn (by simpa only [endpointHalf] using low)
  have coordinates := coordinates_after cn endpoint cross
  have product := mul_nonneg
    (show 0≤s-4200/10441 by linarith only [coordinates.2])
    (show 0≤c+9559/10441-s-4200/10441 by linarith only [cn.2.1])
  have identity : (c+9559/10441)*(c+s-13759/10441)=
      (s-4200/10441)*(c+9559/10441-s-4200/10441) := by
    nlinarith only [cn.2.2]
  have sum : 13759/10441≤c+s := by
    have scaled : 0≤(c+9559/10441)*(c+s-13759/10441) := by rw [identity]; exact product
    have value := nonneg_of_mul_nonneg_right scaled (by linarith only [cb.1] : 0<c+9559/10441)
    linarith only [value]
  refine ⟨coordinates.1,?_,?_,?_,?_⟩ <;>
    nlinarith only [cross,cb.1,sum,coordinates.1]

theorem angle_norm {c s : ℝ} (cn : Normal c s) (low : 21/100≤half c s) :
    capB c s 0^2+capR c s 0^2<1 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have xb := canonical_half_bounds cn
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have cf : c=(1-x^2)/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have sf : s=2*x/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  let a : ℝ := 21/100
  let b : ℝ := 5/12
  let P (z : ℝ) := -1189749*z^4+2308040*z^3-2275898*z^2+863960*z-49749
  let Q := -1189749*(x^2+(a+b)*x+a^2+a*b+b^2)+2308040*(x+a+b)-2275898
  have negative : Q<0 := by dsimp [Q,a,b]; nlinarith only [xb.1,xb.2,sq_nonneg x]
  have chord : (b-x)*P a+(x-a)*P b-(b-a)*P x=(b-a)*(x-a)*(b-x)*Q := by
    dsimp [P,Q]; ring
  have p0 : 0<P a := by norm_num [P,a]
  have p1 : 0<P b := by norm_num [P,b]
  have correction := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (show 0≤b-a by norm_num [a,b])
      (show 0≤x-a by exact sub_nonneg.mpr low))
      (show 0≤b-x by exact sub_nonneg.mpr xb.2)) negative.le
  have first := mul_nonneg (show 0≤b-x by exact sub_nonneg.mpr xb.2) p0.le
  have strict : 0<(b-x)*P a+(x-a)*P b := by
    by_cases zero : x=a
    · have product := mul_pos (show 0<b-a by norm_num [a,b]) p0
      simpa only [zero,sub_self,zero_mul,add_zero] using product
    · have product := mul_pos (show 0<x-a by dsimp [a] at zero ⊢; linarith only [low,zero]) p1
      linarith only [first,product]
  have polynomial : 0<P x := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤b-a by norm_num [a,b]) no
    linarith only [chord,correction,strict,bad]
  have identity : 250000*(1+x^2)^2*(1-capB c s 0^2-capR c s 0^2)=P x := by
    dsimp [capB,capR,centeredD]
    rw [cf,sf]
    dsimp [P]
    field_simp [den.ne']
    <;> ring
  have scaled : 0<250000*(1+x^2)^2*(1-capB c s 0^2-capR c s 0^2) := by
    rw [identity]; exact polynomial
  have positive := pos_of_mul_pos_right scaled
    (show 0≤250000*(1+x^2)^2 by exact mul_nonneg (by norm_num) (sq_nonneg _))
  linarith only [positive]

theorem angle_own_positive {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : 21/100≤half c s) :
    0<1-(543/500)*b-r+(c*r+s*b)*centeredD c s := by
  have norm := angle_norm cn low
  have bound := dot_strict bn.2.2 (by norm_num : (0:ℝ)<1) (by simpa only [one_pow] using norm)
  dsimp [capB,capR] at bound
  nlinarith only [bound]

theorem angle_left {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : 21/100≤half c s) : 0<1-b-r+(c*b+s*r)*centeredD c s := by
  have bounds := centered_D_bounds cn
  have endpoint := angle_endpoint cn low
  let D := centeredD c s
  have weighted := mul_nonneg (show 0≤D by linarith only [bounds.1])
    (show 0≤c+s-13/10 by linarith only [endpoint.2.2.2.1])
  have chord := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤D-27/50 by linarith only [bounds.1])
    (show D+27/50-13/5≤0 by linarith only [bounds.2])
  have identity : (1-c*D)^2+(1-s*D)^2=2-2*(c+s)*D+D^2 := by
    linear_combination D^2*cn.2.2
  have norm : (1-c*D)^2+(1-s*D)^2<1 := by nlinarith only [identity,weighted,chord]
  have bound := dot_strict bn.2.2 (by norm_num : (0:ℝ)<1) (by simpa only [one_pow] using norm)
  dsimp [D] at bound
  nlinarith only [bound]

theorem angle_right_before {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (low : 21/100≤half c s) (order : c*r≤s*b) :
    0<1-(543/500)*b+(s*b-c*r)*centeredD c s := by
  have cb := normal_bounds cn
  have endpoint := angle_endpoint cn low
  have bounds := centered_D_bounds cn
  let D := centeredD c s
  let B := 543/500-s*D
  let R := c*D
  by_cases shallow : s≤1/2
  · have derivative : B*s≤R*c := by
      have identity : R*c-B*s=D-(543/500)*s := by
        dsimp [R,B]
        linear_combination D*cn.2.2
      dsimp [D,centeredD] at identity
      linarith only [identity,shallow,cb.2.1]
    have valueIdentity : B*c+R*s=(543/500)*c := by dsimp [B,R]; ring
    have value : 0≤B*c+R*s := by rw [valueIdentity]; linarith only [cb.1]
    have bound := before b r c s B R bn.2.2 cn.2.2 order derivative value
    rw [valueIdentity] at bound
    dsimp [B,R,D] at bound
    nlinarith only [bound,endpoint.2.2.2.2]
  · have du : D≤33/50 := by dsimp [D,centeredD]; linarith only [shallow,cb.1]
    have chord := mul_nonneg (show 0≤D-27/50 by linarith only [bounds.1])
      (show 0≤33/50-D by linarith only [du])
    have weighted := mul_nonneg (show 0≤D by linarith only [bounds.1])
      (show 0≤s-1/2 by linarith only [shallow])
    have identity : B^2+R^2=(543/500)^2-(543/250)*s*D+D^2 := by
      dsimp [B,R]
      linear_combination D^2*cn.2.2
    have norm : B^2+R^2<1 := by nlinarith only [identity,weighted,chord,du]
    have bound := dot_strict bn.2.2 (by norm_num : (0:ℝ)<1) (by simpa only [one_pow] using norm)
    dsimp [B,R,D] at bound
    nlinarith only [bound]

#print axioms angle_norm
#print axioms angle_left
#print axioms angle_right_before
end N12Compact.C1092MPPMInwardFinal

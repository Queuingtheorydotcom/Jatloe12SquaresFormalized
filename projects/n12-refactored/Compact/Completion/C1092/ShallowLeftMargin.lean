import Compact.Completion.C1092.ShallowCentralScalars
import Compact.Completion.C1092.WallProfileScalars

/-! The coupled left-wall margin uses the same A and K as the bottom
envelope. The strict origin bound is imposed before either face is
eliminated; both relative-angle orders and equality are retained. -/
namespace N12Compact.C1092ShallowLeftMargin
open C977CornerCubic C1092ShallowPositiveScalars C1092ShallowCentralScalars
set_option Elab.async false
noncomputable section

def gamma (a c s A r d : ℝ) : ℝ :=
  d/s*(a*(3/2+c*(c+s)/2)-2*c-
    (r+(c*r-s*d)*A-a*max (c*r-s*d) 0)/(c*d+s*r))-r+(a/2)*(1+r^2+r*d)

theorem margin (a c s A K r d x : ℝ) (side : 1<a)
    (xp : 0<x) (xu : x≤1/4) (cframe : c=cosH x) (sframe : s=sinH x)
    (normal : Normal c s) (wallNormal : Normal d r)
    (Alow : a-c-s≤A) (Ahigh : A≤-s/2)
    (coupled : -(c*r-s*d)*A+(c*d+s*r)*K+a*max (c*r-s*d) 0<r) :
    0< (-(c*r-s*d)*A+(c*d+s*r)*K+a*max (c*r-s*d) 0)-
      (2*r-d*b a c s K-(a/2)*(1+r^2+r*d)) := by
  have cp : 0<c := by rw [cframe]; exact half_cos_pos x xp.le (by linarith only [xu])
  have sp : 0<s := by rw [sframe]; exact half_sin_pos x xp
  have db := normal_bounds wallNormal
  have dp : 0<d := by linarith only [db.1]
  have rn : 0≤r := wallNormal.1
  let k := c*d+s*r
  let tau := c*r-s*d
  let KD := (r+tau*A-a*max tau 0)/k
  have kp : 0<k := add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg sp.le rn)
  have relativeUnit : k^2+tau^2=1 := by
    dsimp [k,tau]
    linear_combination (d^2+r^2)*normal.2.2+wallNormal.2.2
  have ku : k≤1 := by nlinarith only [relativeUnit,sq_nonneg tau,kp]
  have sBound : s≤8/17 := by
    simpa only [←sframe] using (C1092ShallowCentralScalars.bounds x xp xu).2.1
  have ds : s<d := by linarith only [sBound,db.1]
  have coefficient : k-d/s<0 := by
    have weighted := mul_le_mul_of_nonneg_left ku sp.le
    have identity : s*(k-d/s)=s*k-d := by field_simp [sp.ne']
    have negative : s*(k-d/s)<0 := by rw [identity]; linarith only [weighted,ds]
    by_contra failure
    have weak := mul_nonneg sp.le (le_of_not_gt failure)
    exact (not_lt_of_ge weak) negative
  have Ksmall : K<KD := by
    dsimp [KD]
    apply (lt_div_iff₀ kp).mpr
    dsimp [k,tau] at coupled ⊢
    linarith only [coupled]
  have strict := mul_pos_of_neg_of_neg coefficient (sub_neg.mpr Ksmall)
  have identity :
      ((-tau*A+k*K+a*max tau 0)-(2*r-d*b a c s K-(a/2)*(1+r^2+r*d)))-
        gamma a c s A r d=(k-d/s)*(K-KD) := by
    dsimp [gamma,b,KD,k,tau]
    field_simp [sp.ne',kp.ne']
    <;> ring
  have strictGap : gamma a c s A r d<
      (-tau*A+k*K+a*max tau 0)-(2*r-d*b a c s K-(a/2)*(1+r^2+r*d)) := by
    apply sub_pos.mp
    rw [identity]
    exact strict
  let z := C1092WallProfileScalars.half d r
  have quarter := C1092WallProfileScalars.quarter_data d r dp.le rn wallNormal.2.2
  have zn : 0≤z := quarter.1
  have zu : z<1 := by
    dsimp [z,C1092WallProfileScalars.half]
    apply (div_lt_iff₀ (show 0<1+d by linarith only [dp])).mpr
    linarith only [wallNormal.2.1]
  have dspec : d=cosH z := by
    dsimp [cosH]
    apply (eq_div_iff (half_den_pos z).ne').mpr
    nlinarith only [quarter.2.2.2.1]
  have rspec : r=sinH z := by
    dsimp [sinH]
    apply (eq_div_iff (half_den_pos z).ne').mpr
    nlinarith only [quarter.2.2.2.2]
  have tauFactor : tau=2*(z-x)*(1+x*z)/((1+x^2)*(1+z^2)) := by
    have formula := relative_sin_factor x z
    simpa only [relativeSin,←cframe,←sframe,←dspec,←rspec,tau] using formula
  have denominator : 0<(1+x^2)*(1+z^2) := mul_pos (half_den_pos x) (half_den_pos z)
  have weight : 0<2*(1+x*z) := by have product := mul_nonneg xp.le zn; linarith only [product]
  have positive : 0<gamma a c s A r d := by
    by_cases sign : 0≤tau
    · have order : x≤z := by
        apply le_of_not_gt
        intro failure
        have negative : 2*(z-x)*(1+x*z)<0 := by
          have product := mul_neg_of_pos_of_neg weight (sub_neg.mpr failure)
          convert product using 1 <;> ring
        have contrary : tau<0 := by rw [tauFactor]; exact div_neg_of_neg_of_pos negative denominator
        exact (not_lt_of_ge sign) contrary
      have base := left_plus_pos a x z side.le xp xu order zu
      have coefficient' : -(d*tau/(s*k))≤0 := neg_nonpos.mpr
        (div_nonneg (mul_nonneg dp.le sign) (mul_pos sp kp).le)
      have correction := mul_nonneg_of_nonpos_of_nonpos coefficient' (sub_nonpos.mpr Ahigh)
      have baseIdentity : gamma a c s (-s/2) r d=leftPlus a x z := by
        dsimp [gamma]
        rw [max_eq_left sign]
        rw [cframe,sframe,dspec,rspec]
        dsimp [leftPlus,scalarB,relativeCos,relativeSin]
        ring
      have affine : gamma a c s A r d=gamma a c s (-s/2) r d+
          (-(d*tau/(s*k)))*(A-(-s/2)) := by
        dsimp [gamma,k,tau]
        field_simp [sp.ne',kp.ne']
        <;> ring
      rw [affine,baseIdentity]
      exact add_pos_of_pos_of_nonneg base correction
    · have sign' : tau≤0 := (lt_of_not_ge sign).le
      have order : z≤x := by
        apply le_of_not_gt
        intro failure
        have positive : 0<2*(z-x)*(1+x*z) := by
          have product := mul_pos weight (sub_pos.mpr failure)
          convert product using 1 <;> ring
        have contrary : 0<tau := by rw [tauFactor]; exact div_pos positive denominator
        exact (not_lt_of_ge sign') contrary
      have base := left_minus_pos a x z side.le xp xu zn order
      have coefficient' : 0≤-(d*tau/(s*k)) := neg_nonneg.mpr
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos dp.le sign')
          (mul_pos sp kp).le)
      have correction := mul_nonneg coefficient' (sub_nonneg.mpr Alow)
      have baseIdentity : gamma a c s (a-c-s) r d=leftMinus a x z := by
        dsimp [gamma]
        rw [max_eq_right sign']
        rw [cframe,sframe,dspec,rspec]
        dsimp [leftMinus,scalarB,relativeCos,relativeSin]
        ring
      have affine : gamma a c s A r d=gamma a c s (a-c-s) r d+
          (-(d*tau/(s*k)))*(A-(a-c-s)) := by
        dsimp [gamma,k,tau]
        field_simp [sp.ne',kp.ne']
        <;> ring
      rw [affine,baseIdentity]
      exact add_pos_of_pos_of_nonneg base correction
  exact positive.trans strictGap

#print axioms margin
end
end N12Compact.C1092ShallowLeftMargin

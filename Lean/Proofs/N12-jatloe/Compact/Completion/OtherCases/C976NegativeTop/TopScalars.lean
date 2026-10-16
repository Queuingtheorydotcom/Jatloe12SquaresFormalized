import Compact.Completion.OtherCases.C976NegativeTop.QuadrantScalars
import Compact.Completion.CommonCases.CanonicalProjection
import Mathlib.Analysis.Real.Sqrt

/-! Section 4 scalar arguments of C976-NEGATIVE-NE-TOP-ENDING.
The outer low-angle monotonicity is written as its exact two-point
difference, using the same derivative numerator as the prose proof. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
set_option Elab.async false

private theorem endpoint :
    ∃ c₀ s₀ : ℝ,0<c₀ ∧ 0<s₀ ∧ c₀^2+s₀^2=1 ∧ s₀=(2/3)*c₀ ∧
      (9/10)*c₀+(11/25)*s₀<1 ∧
      0<(5/3)*c₀-s₀/3-209/150+(6/5)*s₀^2-(11/30)*c₀*s₀ := by
  let r : ℝ := Real.sqrt 13
  have rp : 0<r := Real.sqrt_pos.2 (by norm_num)
  have rs : r^2=13 := Real.sq_sqrt (by norm_num)
  have rn : r≠0 := ne_of_gt rp
  have rcube := congrArg (fun z : ℝ => z*r) rs
  have margin : 179/50<r := by nlinarith only [rs,rp]
  refine ⟨3/r,2/r,div_pos (by norm_num) rp,div_pos (by norm_num) rp,?_,?_,?_,?_⟩
  · field_simp [rn]
    nlinarith only [rs]
  · ring
  · apply (mul_lt_mul_iff_left₀ rp).mp
    field_simp [rn]
    linarith only [margin]
  · have identity : (5/3)*(3/r)-(2/r)/3-209/150+
        (6/5)*(2/r)^2-(11/30)*(3/r)*(2/r)=r/3-179/150 := by
      field_simp [rn]
      nlinarith only [rs,rcube]
    rw [identity]
    linarith only [margin]

private theorem high_projection (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (slope : (2/3)*c≤s) :
    (9/10)*c+(11/25)*s<1 := by
  obtain ⟨c₀,s₀,c₀p,s₀p,unit₀,slope₀,margin,_⟩ := endpoint
  have cross := mul_nonneg c₀p.le (sub_nonneg.mpr slope)
  have projection := CommonCases.CanonicalProjection.after c s c₀ s₀ (9/10) (11/25)
    unit unit₀ (by rw [slope₀]; nlinarith only [cross])
    (by nlinarith only [slope₀,c₀p]) (by positivity)
  exact lt_of_le_of_lt projection margin

private theorem outer_low (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (slope : s≤(2/3)*c) :
    0<(5/3)*c-s/3-209/150+(6/5)*s^2-(11/30)*c*s := by
  obtain ⟨c₀,s₀,c₀p,s₀p,unit₀,slope₀,_,margin⟩ := endpoint
  have cu : c≤1 := by nlinarith only [unit,sq_nonneg s,cp]
  have c₀u : c₀≤1 := by nlinarith only [unit₀,sq_nonneg s₀,c₀p]
  have cross : c₀*s≤s₀*c := by
    have p := mul_nonneg c₀p.le (sub_nonneg.mpr slope)
    rw [slope₀]
    nlinarith only [p]
  have sine : s≤s₀ := by
    apply le_of_not_gt
    intro high
    have cosine : c<c₀ := by nlinarith only [unit,unit₀,high,cp,c₀p,sp,s₀p]
    have first := mul_pos c₀p (sub_pos.mpr high)
    have last := mul_pos s₀p (sub_pos.mpr cosine)
    nlinarith only [first,last,cross]
  let u := c+c₀
  let v := s+s₀
  have up : 0<u := by dsimp only [u]; linarith only [cp,c₀p]
  have vn : 0≤v := by dsimp only [v]; linarith only [sp,s₀p]
  have uu : u≤2 := by dsimp only [u]; linarith only [cu,c₀u]
  have slopeSum : v≤(2/3)*u := by
    dsimp only [u,v]
    linarith only [slope,slope₀]
  let t := v/u
  have tn : 0≤t := div_nonneg vn up.le
  have tu : t≤2/3 := (div_le_iff₀ up).mpr slopeSum
  have relation : t*u=v := by dsimp only [t]; field_simp [ne_of_gt up]
  have pBound : 11*t^2+22*t-21≤ -13/9 := by
    have product := mul_nonneg (sub_nonneg.mpr tu)
      (show 0≤11*t+88/3 by linarith only [tn])
    nlinarith only [product]
  have derivative : 0≤50*t+10-(u/2)*(72*t-11+11*t^2) := by
    by_cases sign : 72*t-11+11*t^2≤0
    · have product := mul_nonpos_of_nonneg_of_nonpos (show 0≤u/2 by linarith only [up]) sign
      nlinarith only [product,tn]
    · have product := mul_nonneg (show 0≤1-u/2 by linarith only [uu])
        (show 0≤72*t-11+11*t^2 by linarith only [sign])
      nlinarith only [product,pBound]
  let A := (5/3)-(11/60)*v
  let B := -(1/3)+(6/5)*v-(11/60)*u
  have derivativeIdentity :
      30*(A*v-B*u)=u*(50*t+10-(u/2)*(72*t-11+11*t^2)) := by
    dsimp only [A,B]
    simp only [←relation]
    ring
  have positive : 0≤A*v-B*u := by
    have product := mul_nonneg up.le derivative
    nlinarith only [product,derivativeIdentity]
  have circle : (c-c₀)*u=(s₀-s)*v := by
    dsimp only [u,v]
    nlinarith only [unit,unit₀]
  have identity :
      u*((5/3)*c-s/3-209/150+(6/5)*s^2-(11/30)*c*s-
        ((5/3)*c₀-s₀/3-209/150+(6/5)*s₀^2-(11/30)*c₀*s₀))=
      (s₀-s)*(A*v-B*u) := by
    have weighted := congrArg (fun z : ℝ => A*z) circle
    dsimp only [A,B,u,v] at weighted ⊢
    nlinarith only [weighted]
  have product := mul_nonneg (sub_nonneg.mpr sine) positive
  have difference : 0≤(5/3)*c-s/3-209/150+(6/5)*s^2-(11/30)*c*s-
        ((5/3)*c₀-s₀/3-209/150+(6/5)*s₀^2-(11/30)*c₀*s₀) := by
    apply le_of_not_gt
    intro negative
    have bad := mul_neg_of_pos_of_neg up negative
    linarith only [identity,product,bad]
  linarith only [difference,margin]

private theorem outer_coefficients (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (order : s≤c) (unit : c^2+s^2=1) :
    0<c+s-(37/50)*c^2-(11/25)*s^2-c*s := by
  have arc := (CommonCases.CanonicalScalars.bounds c s cp sp.le order unit).2.2.2.2
  have positive : 0<(1/10)*(c-s)^2+(4/25)*c^2+(23/50)*s^2 := by positivity
  nlinarith only [arc,positive,unit]

theorem top_outer_margin (c s C S : ℝ) (cp : 0<c) (sp : 0<s)
    (order : s≤c) (unit : c^2+s^2=1) (Cp : 0<C) (Sn : 0≤S)
    (unitW : C^2+S^2=1) (ratio : (2/3)*S≤C) (dSign : 0≤c*C-s*S) :
    0<(c*S+s*C)*(1-c-(11/25)*s)+(c*C-s*S)*(1-(37/50)*c)+
      (1-(1-S)/C-(18/25)*S) := by
  let A := c+s-(37/50)*c^2-(11/25)*s^2-c*s
  let B := c-s-c^2+(3/10)*c*s
  have Ap : 0<A := outer_coefficients c s cp sp order unit
  have expansion :
      (c*S+s*C)*(1-c-(11/25)*s)+(c*C-s*S)*(1-(37/50)*c)=C*A+S*B := by
    dsimp only [A,B]
    ring
  rw [expansion]
  rcases Sn.eq_or_lt with zero | Sp
  · have sz : S=0 := zero.symm
    have co : C=1 := by nlinarith only [unitW,Cp,sz]
    simpa only [sz,co,mul_zero,zero_mul,add_zero,sub_zero,div_one,sub_self,one_mul] using Ap
  · have delta := wall_delta C S Cp Sp unitW
    by_cases slope : s≤(2/3)*c
    · have small : 0<(2/3)*A+B+1/10 := by
        have margin := outer_low c s cp sp unit slope
        dsimp only [A,B]
        nlinarith only [margin,unit]
      have first := mul_nonneg (sub_nonneg.mpr ratio) Ap.le
      have last := mul_pos Sp small
      nlinarith only [first,last,delta]
    · have projection := high_projection c s cp sp unit (le_of_not_ge slope)
      have exactIdentity : s*A+c*B+(1/10)*c=1-(9/10)*c-(11/25)*s := by
        dsimp only [A,B]
        linear_combination (1-c-(11/25)*s)*unit
      have first := mul_nonneg dSign Ap.le
      have last := mul_pos Sp (show 0<1-(9/10)*c-(11/25)*s by linarith only [projection])
      have scaled : 0<c*(C*A+S*B+(1/10)*S) := by
        clear_value A B
        have weighted := congrArg (fun z : ℝ => S*z) exactIdentity
        nlinarith only [first,last,weighted]
      have lower := (mul_pos_iff_of_pos_left cp).mp scaled
      linarith only [lower,delta]

theorem top_mixed_margin (c s C S : ℝ) (cp : 0<c) (sp : 0<s)
    (order : s≤c) (unit : c^2+s^2=1) (Cp : 0<C) (Sn : 0≤S)
    (unitW : C^2+S^2=1) (ratio : (2/3)*S≤C) (angle : s<(13/25)*c) :
    0<(c*S+s*C)*(1-c-(11/25)*s)+(c*C-s*S)*(1+(1/2)*s-c)+
      (1-(1-S)/C-(18/25)*S) := by
  let A := c+s-c^2-(11/25)*s^2-(1/2)*c*s
  let B := c-s-c^2-(1/2)*s^2+(14/25)*c*s
  have arc := (CommonCases.CanonicalScalars.bounds c s cp sp.le order unit).2.2.2.2
  have cross := mul_pos cp sp
  have Ap : 0<A := by dsimp only [A]; nlinarith only [arc,unit,cross,sq_nonneg s]
  have angular := mul_nonneg (show 0≤(13/25)*c-s by linarith only [angle])
    (show 0≤(13/25)*c+s by linarith only [cp,sp])
  have clower : 7/8≤c := by nlinarith only [angular,unit,cp]
  have supper : s≤1/2 := by nlinarith only [angular,unit,sp]
  have sSquare : s^2≤1/4 := by nlinarith only [supper,sp]
  have denominator : 0<1+c := by linarith only [cp]
  have coeffOne : -(27/200)≤17*c/75-1/3 := by linarith only [clower]
  have coeffTwo : -(7/450)≤131/150-5/(3*(1+c)) := by
    have quotient : 5/(3*(1+c))≤8/9 :=
      (div_le_iff₀ (by linarith only [denominator])).mpr (by linarith only [clower])
    linarith only [quotient]
  have identity : (2/3)*A+B=
      s*(17*c/75-1/3)+s^2*(131/150-5/(3*(1+c))) := by
    have circle : c-1= -s^2/(1+c) := by
      apply (eq_div_iff (ne_of_gt denominator)).mpr
      nlinarith only [unit]
    calc
      _ = s*(17*c/75-1/3)+(131/150)*s^2+(5/3)*(c-1) := by
        dsimp only [A,B]
        linear_combination -(5/3)*unit
      _ = _ := by
        rw [circle]
        field_simp [denominator.ne']
        ring
  have first := mul_nonneg sp.le (sub_nonneg.mpr coeffOne)
  have last := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr coeffTwo)
  have lower : -(257/3600)≤(2/3)*A+B := by
    rw [identity]
    nlinarith only [first,last,supper,sSquare]
  have expansion :
      (c*S+s*C)*(1-c-(11/25)*s)+(c*C-s*S)*(1+(1/2)*s-c)=C*A+S*B := by
    dsimp only [A,B]
    ring
  rw [expansion]
  rcases Sn.eq_or_lt with zero | Sp
  · have sz : S=0 := zero.symm
    have co : C=1 := by nlinarith only [unitW,Cp,sz]
    simpa only [sz,co,mul_zero,zero_mul,add_zero,sub_zero,div_one,sub_self,one_mul] using Ap
  · have delta := wall_delta C S Cp Sp unitW
    have first := mul_nonneg (sub_nonneg.mpr ratio) Ap.le
    have last := mul_nonneg Sp.le (show 0≤(2/3)*A+B+257/3600 by linarith only [lower])
    nlinarith only [first,last,delta,Sp]

theorem top_negative_margin (c s C S : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (Cp : 0<C) (Sn : 0≤S)
    (unitW : C^2+S^2=1) (ratio : (2/3)*S≤C) (dSign : c*C-s*S<0) :
    0<(c*S+s*C)*(1-c-(11/25)*s)+(1-(1-S)/C-(18/25)*S) := by
  have Sp : 0<S := by
    have product := mul_pos cp Cp
    nlinarith only [dSign,product,Sn,sp]
  have slope : (2/3)*c≤s := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr ratio)
    have scaled : 0<S*(s-(2/3)*c) := by nlinarith only [first,dSign]
    have gap := (mul_pos_iff_of_pos_left Sp).mp scaled
    linarith only [gap]
  have projection := high_projection c s cp sp unit slope
  have Slarge : c<S := by
    have product := mul_neg_of_neg_of_pos dSign
      (show 0<c*C+s*S by positivity)
    have identity : (c*C-s*S)*(c*C+s*S)=c^2-S^2 := by
      linear_combination c^2*unitW-S^2*unit
    nlinarith only [product,identity,cp,Sp]
  let k := c*S+s*C
  have kp : 0<k := by dsimp only [k]; positivity
  have ku : k≤1 := by
    have identity : (c*C-s*S)^2+k^2=1 := by
      dsimp only [k]
      calc
        _ = (c^2+s^2)*(C^2+S^2) := by ring
        _ = 1 := by rw [unit,unitW]; norm_num
    nlinarith only [identity,sq_nonneg (c*C-s*S),kp]
  have delta := wall_delta C S Cp Sp unitW
  change 0<k*(1-c-(11/25)*s)+(1-(1-S)/C-(18/25)*S)
  by_cases base : 0≤1-c-(11/25)*s
  · have product := mul_nonneg kp.le base
    linarith only [product,delta,Sp]
  · have product := mul_nonneg (sub_nonneg.mpr ku)
      (show 0≤ -(1-c-(11/25)*s) by linarith only [base])
    nlinarith only [product,delta,Slarge,projection]

#print axioms top_outer_margin
#print axioms top_mixed_margin
#print axioms top_negative_margin
end N12Compact.Completion.OtherCases.C976NegativeTop

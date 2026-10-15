import Compact.Completion.C1092.MPPMActualNonordinaryScalars
import Compact.Completion.CommonCases.CanonicalProjection

/-! The two complete endpoint margins of ELBOW-EXCLUSION §§2.4–2.5.
The rational unit vector (91,60)/109 is the printed half-angle 3/10.
Exact unit-circle projection monotonicity replaces both derivatives. -/
namespace N12Compact.C1092MPPMActualNonordinary
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private theorem half_form (c s : ℝ) (cn : Normal c s) (cp : 0<c) :
    c=(1-(s/(1+c))^2)/(1+(s/(1+c))^2) ∧
      s=2*(s/(1+c))/(1+(s/(1+c))^2) := by
  let z := s/(1+c)
  have den : 0<1+c := by linarith only [cp]
  have dz : 0<1+z^2 := by positivity
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [den.ne']
  have unitAngle : s*z=1-c := by
    dsimp [z]; field_simp [den.ne']; nlinarith only [cn.2.2]
  constructor
  · apply (eq_div_iff dz.ne').mpr
    have prod := congrArg (fun a : ℝ => a*z) angle
    dsimp at prod
    nlinarith only [prod,unitAngle]
  · apply (eq_div_iff dz.ne').mpr
    have prod := congrArg (fun a : ℝ => a*z) unitAngle
    dsimp at prod
    nlinarith only [prod,angle]

theorem far_angle (d t : ℝ) (dn : Normal d t) (width : 1<t+(263/500)*d) :
    60*d<91*t ∧ d<91/109 := by
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  have cross : 60*d<91*t := by
    apply lt_of_not_ge
    intro no
    have bound := CommonCases.CanonicalProjection.before d t (91/109) (60/109)
      (263/500) 1 dn.2.2 (by norm_num)
      (by linarith only [no]) (by norm_num) (by norm_num)
    norm_num at bound
    linarith only [width,bound]
  have product := mul_pos (sub_pos.mpr cross)
    (show 0<91*t+60*d by linarith only [dp,dn.1])
  have bound : d<91/109 := by
    apply lt_of_not_ge
    intro high
    have square := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤d+91/109 by linarith only [dp])
    nlinarith only [product,square,dn.2.2]
  exact ⟨cross,bound⟩

theorem far_source_transverse (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 24/25<c) (sp : 0<s) (small : s<7/25) (sum : c+s<31/25)
    (angle : d≤91/109) :
    0<1-(7/20)*(c+s)+(c*d-s*t)*(1-(543/500)*d)+(c*t+s*d)*(1-d-t) := by
  have rel := relative_bounds c s d t cn dn cp sp small
  have arc := normal_sum d t dn
  have first := mul_nonneg rel.1.le
    (show 0≤1-(543/500)*d by linarith only [angle])
  have last := mul_nonneg (sub_nonneg.mpr rel.2.2.2)
    (show 0≤d+t-1 by linarith only [arc.1])
  nlinarith only [first,last,sum,arc.2.1]

/-- The whole first segment-source margin, including z=0 in its
endpoint identity, though the actual elbow has positive sine. -/
theorem far_transverse_segment (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 24/25<c) (sp : 0<s) (small : s<7/25) (sum : c+s<31/25)
    (half : s/(1+c)<7/50) (cross : 60*d≤91*t) :
    0<1-d-t+(c*d-s*t)*(1-c-(2/5)*s)+(c*t+s*d)*(1-(543/500)*s) := by
  let A := 2-c-s+(43/500)*s^2+(2/5)*c*s
  let B := 1-c+s+(43/500)*c*s-(2/5)*s^2
  let z := s/(1+c)
  have cb := normal_bounds cn
  have cps : 0<c := by linarith only [cp]
  have den : 0<1+c := by linarith only [cp]
  have zp : 0<z := div_pos sp den
  have zh : z<7/50 := half
  have dz : 0<1+z^2 := by positivity
  have cs := mul_nonneg cps.le sp.le
  have aLow : 19/25<A := by dsimp [A]; nlinarith only [sum,cs,sq_nonneg s]
  have bLow : 0<B := by
    have product := mul_pos sp (show 0<1-(2/5)*s by linarith only [small])
    dsimp [B]; nlinarith only [product,cs,cb.2.1]
  have bHigh : B<7/20 := by
    have product := mul_nonneg (sub_nonneg.mpr cb.2.1) sp.le
    dsimp [B]
    nlinarith only [product,cp,small,sq_nonneg s]
  have projected := CommonCases.CanonicalProjection.after d t (91/109) (60/109)
    A B dn.2.2 (by norm_num) (by linarith only [cross])
    (by linarith only [aLow,bHigh]) (by linarith only [aLow,bLow])
  have forms := half_form c s cn cps
  have cv : c=(1-z^2)/(1+z^2) := forms.1
  have sv : s=2*z/(1+z^2) := forms.2
  have identity : 1-A*(91/109)-B*(60/109)=
      (10*z+3)*(750-3380*z+2879*z^2-3550*z^3)/(13625*(1+z^2)^2) := by
    dsimp [A,B]
    rw [cv,sv]
    field_simp [dz.ne']
    ring
  have polynomial : 0<750-3380*z+2879*z^2-3550*z^3 := by
    have last := mul_nonneg (sq_nonneg z)
      (show 0≤2879-3550*z by linarith only [zh])
    nlinarith only [last,zh]
  have endpoint : 0<1-A*(91/109)-B*(60/109) := by
    rw [identity]
    exact div_pos (mul_pos (by linarith only [zp]) polynomial) (by positivity)
  have expansion :
      1-d-t+(c*d-s*t)*(1-c-(2/5)*s)+(c*t+s*d)*(1-(543/500)*s)=1-A*d-B*t := by
    dsimp [A,B]
    linear_combination -d*cn.2.2
  rw [expansion]
  linarith only [projected,endpoint]

/-- The whole oblique segment-source margin. The polynomial is the
literal quartic (16), and its middle two terms are grouped positively. -/
theorem far_oblique_segment (c s d t : ℝ) (cn : Normal c s) (dn : Normal d t)
    (cp : 24/25<c) (sp : 0<s) (small : s<7/25)
    (half : s/(1+c)<7/50) (cross : 60*d≤91*t) :
    0<((13/50)*s+(43/500)*c)*(1-d-t-(13/50)*s*(c*d-s*t))+
      (c*t+s*d)*(((13/50)*s+(43/500)*c)+((13/50)*c-(43/500)*s)+
        (13/50)*s*((13/50)*c-(43/500)*s)-7059/25000) := by
  let gamma := (13/50)*s+(43/500)*c
  let A := (43/500)*c+(7059/12500)*s-(173/500)*c*s-(87/500)*s^2
  let B := (9209/25000)*c-173/500+(481/2500)*s-(87/500)*c*s+(173/500)*s^2
  let z := s/(1+c)
  have cb := normal_bounds cn
  have cps : 0<c := by linarith only [cp]
  have den : 0<1+c := by linarith only [cp]
  have zp : 0<z := div_pos sp den
  have zh : z<7/50 := half
  have dz : 0<1+z^2 := by positivity
  have csgap := mul_nonneg (sub_nonneg.mpr cb.2.1) sp.le
  have sgap := mul_nonneg (sub_nonneg.mpr small.le) sp.le
  have aLow : 2/25<A := by
    dsimp [A]
    nlinarith only [csgap,sgap,cp,sp]
  have bLow : 0<B := by
    dsimp [B]
    nlinarith only [csgap,cp,sp,sq_nonneg s]
  have cBound : c≤1-s^2/2 := by nlinarith only [cn.2.2,sq_nonneg (1-c)]
  have csgap' := mul_nonneg (show 0≤c-24/25 by linarith only [cp]) sp.le
  have square := mul_nonneg (sub_nonneg.mpr small.le)
    (show 0≤7/25+s by linarith only [sp])
  have bHigh : B<43/1000 := by
    dsimp [B]
    nlinarith only [cBound,csgap',small,square]
  have projected := CommonCases.CanonicalProjection.after d t (91/109) (60/109)
    A B dn.2.2 (by norm_num) (by linarith only [cross])
    (by linarith only [aLow,bHigh]) (by linarith only [aLow,bLow])
  have forms := half_form c s cn cps
  have cv : c=(1-z^2)/(1+z^2) := forms.1
  have sv : s=2*z/(1+z^2) := forms.2
  have identity : gamma-A*(91/109)-B*(60/109)=
      (129105*z^4-478247*z^3+68175*z^2+45828*z+645)/(340625*(1+z^2)^2) := by
    dsimp [gamma,A,B]
    rw [cv,sv]
    field_simp [dz.ne']
    ring
  have polynomial : 0<129105*z^4-478247*z^3+68175*z^2+45828*z+645 := by
    have middle := mul_nonneg (sq_nonneg z)
      (show 0≤68175-478247*z by linarith only [zh])
    nlinarith only [middle,sq_nonneg (z^2),zp]
  have endpoint : 0<gamma-A*(91/109)-B*(60/109) := by
    rw [identity]
    exact div_pos polynomial (by positivity)
  have expansion :
      ((13/50)*s+(43/500)*c)*(1-d-t-(13/50)*s*(c*d-s*t))+
        (c*t+s*d)*(((13/50)*s+(43/500)*c)+((13/50)*c-(43/500)*s)+
          (13/50)*s*((13/50)*c-(43/500)*s)-7059/25000)=gamma-A*d-B*t := by
    dsimp [gamma,A,B]
    linear_combination (-(559/25000)*s*d+((169/2500)*s+173/500)*t)*cn.2.2
  rw [expansion]
  linarith only [projected,endpoint]

end N12Compact.C1092MPPMActualNonordinary
